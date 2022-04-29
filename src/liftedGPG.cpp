#include "liftedGPG.h"

#include "gpg.h"

void assignGroundNosToDeleteEffects(const Domain & domain, std::vector<GpgPlanningGraph::ResultType *> & groundedTasksPg,std::set<GpgPlanningGraph::StateType> & reachableFacts){
	for (GpgPlanningGraph::ResultType * groundedTask : groundedTasksPg){
		// assign fact NOs to delete effects
		for (const PredicateWithArguments & delEffect : domain.tasks[groundedTask->taskNo].effectsDel){
			GpgPlanningGraph::StateType delState;
			delState.setHeadNo (delEffect.getHeadNo ());
			for (int varIdx : delEffect.arguments)
			{
				delState.arguments.push_back (groundedTask->arguments[varIdx]);
			}

			// Check if we already know this fact
			std::set<GpgPlanningGraph::StateType>::iterator factIt;
			if ((factIt = reachableFacts.find (delState)) != reachableFacts.end())
			{
				// If this delete effect occurs in the list of reachable facts, then add it to the effect list. If not, it can never be true 
				groundedTask->groundedDelEffects.push_back(factIt->groundedNo);
			}
		
		}
	}
}


std::tuple<std::vector<Fact>, std::vector<GroundedTask>, std::vector<GroundedMethod>> run_lifted_HTN_GPG(const Domain & domain, const Problem & problem, grounding_configuration & config, given_plan_typing_information & given_typing){
	std::unique_ptr<HierarchyTyping> hierarchyTyping;
	// don't do hierarchy typing for classical instances
	if (problem.initialAbstractTask != -1 && config.enableHierarchyTyping)
		hierarchyTyping = std::make_unique<HierarchyTyping> (domain, problem, config, given_typing, true, false);

	if (!config.quietMode) std::cerr << "Running PG." << std::endl;
	GpgPlanningGraph pg (domain, problem);
	std::vector<GpgPlanningGraph::ResultType *> groundedTasksPg;
	std::set<Fact> reachableFacts;
	runGpg (pg, groundedTasksPg, reachableFacts, hierarchyTyping.get (), config);
	
	if (!config.quietMode) std::cerr << "PG done. Postprocessing" << std::endl;
	assignGroundNosToDeleteEffects(domain, groundedTasksPg, reachableFacts);
	validateGroundedListP (groundedTasksPg);

	if (!config.quietMode) std::cerr << "PG postprocessing done." << std::endl;
	if (!config.quietMode) std::cerr << "Calculated [" << groundedTasksPg.size () << "] grounded tasks and [" << reachableFacts.size () << "] reachable facts." << std::endl;
	

	/*for (GroundedTask* out : groundedTasksPg){
		std::cout << domain.tasks[out->taskNo].name;
		std::cout << "[";
		bool first = true;
		for (int a : out->arguments){
			if (!first) std::cout << ",";
			std::cout << domain.constants[a];
			first = false;
		}
		std::cout << "]";
		std::cout << std::endl;
	}*/


	if (problem.initialAbstractTask == -1){
		// create facts in the correct order
		std::vector<Fact> reachableFactsList  (reachableFacts.size ());
		for (const Fact & fact : reachableFacts)
			reachableFactsList[fact.groundedNo] = fact;
	
		std::vector<GroundedMethod> no_methods;
		
		std::vector<GpgPlanningGraph::ResultType> returnTasks;
		for (size_t i = 0; i < groundedTasksPg.size(); i++){
			returnTasks.push_back(*groundedTasksPg[i]);
			delete groundedTasksPg[i];
		}

		return std::make_tuple(reachableFactsList, returnTasks, no_methods);
	}

	DEBUG(std::cerr << "After lifted PG:" << std::endl;
	for (size_t taskIdx = 0; taskIdx < groundedTasksPg.size (); ++taskIdx)
	{
		const GroundedTask * task = groundedTasksPg[taskIdx];
		assert (task->taskNo < domain.nPrimitiveTasks);
		assert (task->groundedPreconditions.size () == domain.tasks[task->taskNo].preconditions.size ());
		assert (task->groundedDecompositionMethods.size () == 0);
		std::cerr << "    Task " << taskIdx << " (" << task->groundedNo << ", " << ((task->taskNo < domain.nPrimitiveTasks) ? "primitive" : " abstract") << "): " << task->groundedPreconditions.size () << " grounded preconditions (vs " << domain.tasks[task->taskNo].preconditions.size () << "), "
			<< task->groundedDecompositionMethods.size () << " grounded decomposition methods (vs " << domain.tasks[task->taskNo].decompositionMethods.size () << ")." << std::endl;
	});


	DEBUG (
	for (const auto & fact : reachableFacts)
	{
		std::cerr << "Grounded fact #" << fact.groundedNo << " (" << domain.predicates[fact.predicateNo].name << ")" << std::endl;
		std::cerr << std::endl;
	}
	);

	std::vector<int> groundedTasksByTask (domain.nTotalTasks);
	for (const GroundedTask * task : groundedTasksPg)
		++groundedTasksByTask[task->taskNo];

	for (const auto & _method : domain.decompositionMethods)
	{
		DecompositionMethod & method = const_cast<DecompositionMethod &> (_method);
		std::vector<std::pair<size_t, int>> subtasksWithFrequency;
		for (size_t subtaskIdx = 0; subtaskIdx < method.subtasks.size (); ++subtaskIdx)
		{
			const TaskWithArguments & subtask = method.subtasks[subtaskIdx];
			//subtasksWithFrequency.push_back (std::make_pair (groundedTasksByTask[subtask.taskNo], subtaskIdx));
			subtasksWithFrequency.push_back (std::make_pair (domain.tasks[subtask.taskNo].variableSorts.size(), subtaskIdx));
		}
		std::sort (subtasksWithFrequency.begin (), subtasksWithFrequency.end (), std::greater<std::pair<size_t, int>> ());
		std::vector<TaskWithArguments> subtasks (method.subtasks.size ());
		std::vector<int> oldSubtaskIDToNewSubTaskID (method.subtasks.size());
		for (size_t subtaskIdx = 0; subtaskIdx < method.subtasks.size (); ++subtaskIdx)
		{
			const auto & foo = subtasksWithFrequency[subtaskIdx];
			subtasks[subtaskIdx] = method.subtasks[foo.second];
			oldSubtaskIDToNewSubTaskID[foo.second] = subtaskIdx;
		}
		method.subtasks = subtasks;
		std::vector<std::pair<int,int>> newOrdering;
		for (auto & ord : method.orderingConstraints){
			newOrdering.push_back(std::make_pair(oldSubtaskIDToNewSubTaskID[ord.first], oldSubtaskIDToNewSubTaskID[ord.second]));
		}
		method.orderingConstraints = newOrdering;
	}

	if (!config.quietMode) std::cerr << "Running TDG." << std::endl;
	GpgTdg tdg (domain, problem, groundedTasksPg);
	std::vector<GpgTdg::ResultType *> groundedMethods;
	std::set<GpgTdg::StateType> groundedTaskSetTdg;
	runGpg (tdg, groundedMethods, groundedTaskSetTdg, hierarchyTyping.get (), config);
	if (!config.quietMode) std::cerr << "TDG done." << std::endl;
	if (!config.quietMode) std::cerr << "Calculated [" << groundedTaskSetTdg.size () << "] grounded tasks and [" << groundedMethods.size () << "] grounded decomposition methods." << std::endl;

	validateGroundedListP (groundedMethods);

	// Order grounded tasks correctly
	std::vector<GroundedTask *> groundedTasksTdg (groundedTaskSetTdg.size ());
	auto it = groundedTaskSetTdg.begin();
	while (it != groundedTaskSetTdg.end()){
		GroundedTask * t = new GroundedTask();
		*t = *it;
		groundedTasksTdg[it->groundedNo] = t;
		it = groundedTaskSetTdg.erase(it);
	}

	// Add grounded decomposition methods to the abstract tasks
	for (const GroundedMethod * method : groundedMethods)
		for (auto abstractGroundedTaskNo : method->groundedAddEffects)
			groundedTasksTdg[abstractGroundedTaskNo]->groundedDecompositionMethods.push_back (method->groundedNo);

	validateGroundedListP (groundedTasksTdg);

	DEBUG (
	for (const auto * task : groundedTasksTdg)
	{
		std::cerr << "Grounded task #" << task->groundedNo << " (" << domain.tasks[task->taskNo].name << ")" << std::endl;
		std::cerr << "Grounded decomposition methods:";
		for (const auto & prec : task->groundedDecompositionMethods)
			std::cerr << " " << prec;
		std::cerr << std::endl;
		std::cerr << "Grounded preconditions:";
		for (const auto & prec : task->groundedPreconditions)
			std::cerr << " " << prec;
		std::cerr << std::endl;
		std::cerr << "Grounded add effects:";
		for (const auto & prec : task->groundedAddEffects)
			std::cerr << " " << prec;
		std::cerr << std::endl;
		std::cerr << std::endl;
	}

	for (const auto * method : groundedMethods)
	{
		std::cerr << "Grounded method #" << method->groundedNo << " (" << domain.decompositionMethods[method->methodNo].name << ")" << std::endl;
		std::cerr << "Grounded preconditions:";
		for (const auto & prec : method->groundedPreconditions)
			std::cerr << " " << prec << " (" << domain.tasks[groundedTasksTdg[prec]->taskNo].name << ")";
		std::cerr << std::endl;
		std::cerr << "Grounded add effects:";
		for (const auto & prec : method->groundedAddEffects)
			std::cerr << " " << prec << " (" << domain.tasks[groundedTasksTdg[prec]->taskNo].name << ")";
		std::cerr << std::endl;
		std::cerr << std::endl;
	}
	);

	// create facts in the correct order
	std::vector<Fact> reachableFactsList  (reachableFacts.size ());
	for (const Fact & fact : reachableFacts)
		reachableFactsList[fact.groundedNo] = fact;

	// Perform DFS
	if (!config.quietMode) std::cerr << "Performing DFS." << std::endl;
	// we first have to translate the tasks into pointers to save memory ...
	std::vector<GroundedTask> reachableTasksDfs;
	std::vector<GroundedMethod> reachableMethodsDfs;
	std::unordered_set<int> reachableCEGuards;
	tdgDfs (reachableTasksDfs, reachableMethodsDfs, groundedTasksTdg, groundedMethods, reachableFactsList, reachableCEGuards, domain, problem);

	// add primitive tasks from conditional effects as reachable
	for (GroundedTask * gt : groundedTasksTdg){
		if (!gt) continue;
		if (!domain.tasks[gt->taskNo].isCompiledConditionalEffect) continue;
		
		for (int & pre : gt->groundedPreconditions)
			if (reachableCEGuards.count(pre)){
				gt->groundedNo = reachableTasksDfs.size();
				reachableTasksDfs.push_back(*gt);
			}
	}


	if (!config.quietMode) std::cerr << "DFS done." << std::endl;
	if (!config.quietMode) std::cerr << "After DFS: " << reachableTasksDfs.size () << " tasks, " << reachableMethodsDfs.size () << " methods." << std::endl;

	DEBUG(size_t tmp = 0;
	for (const auto & t : reachableTasksDfs)
		if (t.taskNo < domain.nPrimitiveTasks)
			++tmp;
	std::cerr << "Primitive: " << tmp << std::endl;);


	// validate all lists
	validateGroundedList (reachableTasksDfs);
	validateGroundedList (reachableMethodsDfs);
	validateGroundedList (reachableFactsList);


	return std::make_tuple(reachableFactsList, reachableTasksDfs, reachableMethodsDfs);
}
