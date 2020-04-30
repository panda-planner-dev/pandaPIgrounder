#include <algorithm>
#include <iostream>
#include <set>
#include <vector>

#include <cassert>

#include "debug.h"
#include "model.h"
#include "hierarchy-typing.h"

template<typename T>
static std::set<T> intersect (const std::set<T> & a, const std::set<T> & b)
{
	std::set<T> result;
	std::set_intersection (a.begin (), a.end (), b.begin (), b.end (), std::inserter (result, result.begin ()));
	return result;
}

/**
 * @brief Reduces the set of possible constants for a task/method by applying variable constraints.
 *
 * If a constraint requires that variables a and b be equal, then only those constants that are valid for both a and b are valid.
 * If a constraint requires that variables a and b *not* be equal, and there is only one allowed value for a, then we can remove the allowed value for a from the set of allowed values for b (or vice versa).
 *
 * This function will repeatedly apply the constraints until these rules yield no further reduction.
 */
static void applyConstraints (PossibleConstants & possibleConstants, const std::vector<VariableConstraint> & constraints)
{
	bool changed;
	do
	{
		changed = false;
		for (const VariableConstraint & constraint : constraints)
		{
			if (constraint.type == VariableConstraint::Type::EQUAL)
			{
				// Both variables must be equal; reduce the set of possible constants to the intersection.
				const auto & intersection = intersect (possibleConstants[constraint.var1], possibleConstants[constraint.var2]);

				// Comparing the size of the sets is faster than comparing the sets themselves
				if (intersection.size () < possibleConstants[constraint.var1].size () || intersection.size () < possibleConstants[constraint.var2].size ())
					changed = true;

				possibleConstants[constraint.var1] = intersection;
				possibleConstants[constraint.var2] = intersection;
			}
			else if (constraint.type == VariableConstraint::Type::NOT_EQUAL)
			{
				// Both variables may not be equal; if any of them only has one possible value, remove it from the other.
				size_t erased = 0;
				if (possibleConstants[constraint.var1].size () == 1)
					erased += possibleConstants[constraint.var2].erase (*possibleConstants[constraint.var1].begin ());
				if (possibleConstants[constraint.var2].size () == 1)
					erased += possibleConstants[constraint.var1].erase (*possibleConstants[constraint.var2].begin ());

				if (erased > 0)
					changed = true;
			}
		}
	}
	while (changed);
}

HierarchyTyping::HierarchyTyping (const Domain & domain, const Problem & problem, bool withStaticPreconditionChecking, bool quietMode) : domain(&domain), possibleConstantsPerTask (domain.nTotalTasks), possibleConstantsPerMethod (domain.decompositionMethods.size ())
{
	assert(domain.tasks.size() > problem.initialAbstractTask);
	
	std::vector<bool> staticPredicates;
	std::vector<std::vector<std::map<int,std::vector<int>>>> factsPerPredicate (domain.predicates.size());
	
	if (withStaticPreconditionChecking){
		if (!quietMode) std::cout << "Starting Preparations for Hierarchy Typing" << std::endl;
	
		// determine predicates that are definitely static s.t. we can already prune using them here
		for (size_t predicateID = 0; predicateID < domain.predicates.size(); predicateID++)
			staticPredicates.push_back(true);
		
		for (size_t taskID = 0; taskID < domain.nPrimitiveTasks; taskID++){
			for (size_t addID = 0; addID < domain.tasks[taskID].effectsAdd.size(); addID++)
				staticPredicates[domain.tasks[taskID].effectsAdd[addID].predicateNo] = false;
			for (size_t delID = 0; delID < domain.tasks[taskID].effectsDel.size(); delID++)
				staticPredicates[domain.tasks[taskID].effectsDel[delID].predicateNo] = false;
		}
	
		DEBUG(
			for (size_t predicateID = 0; predicateID < domain.predicates.size(); predicateID++)
				std::cout << "Predicate " << predicateID << " " << domain.predicates[predicateID].name << " is static" << std::endl;
		);
	
		// quick filter for init
		for (size_t predicateID = 0; predicateID < domain.predicates.size(); predicateID++)
			if (staticPredicates[predicateID])
				factsPerPredicate[predicateID].resize(domain.predicates[predicateID].argumentSorts.size());	

		for (size_t factID = 0; factID < problem.init.size(); factID++){
			if (staticPredicates[problem.init[factID].predicateNo]){
				const Fact & f = problem.init[factID];
				for (size_t arg = 0; arg < f.arguments.size(); arg++)
					factsPerPredicate[problem.init[factID].predicateNo][arg][f.arguments[arg]].push_back(factID);
			}
		}
	}


	const Task & topTask = domain.tasks[problem.initialAbstractTask];

	// Initially determine possible constants for the top task
	PossibleConstants topTaskPossibleConstants (topTask.variableSorts.size ());
	for (size_t varIdx = 0; varIdx < topTask.variableSorts.size (); ++varIdx)
		topTaskPossibleConstants[varIdx] = domain.sorts[varIdx].members;
	applyConstraints (topTaskPossibleConstants, topTask.variableConstraints);
	
	if (!quietMode) std::cout << "done." << std::endl;

	if (!quietMode) std::cout << "Starting Hierarchy Typing" << std::endl;
	// Start the DFS at the top task
	taskDfs (domain, problem, withStaticPreconditionChecking, staticPredicates, factsPerPredicate, problem.initialAbstractTask, topTaskPossibleConstants);
	if (!quietMode) std::cout << "Finished Hierarchy Typing" << std::endl;

	DEBUG(
	for (size_t taskID = 0; taskID < domain.nPrimitiveTasks; taskID++)
		std::cout << "Task " << taskID << " " << domain.tasks[taskID].name << " " << possibleConstantsPerTask[taskID].size() << std::endl;
	
	for (size_t methodID = 0; methodID < domain.decompositionMethods.size(); methodID++)
		std::cout << "Method " << methodID << " " << domain.decompositionMethods[methodID].name << " " << possibleConstantsPerMethod[methodID].size() << std::endl;
	);

	// splitting
	possibleConstantsSplitted.resize(domain.nPrimitiveTasks);
	for (size_t taskID = 0; taskID < domain.nPrimitiveTasks; taskID++){
		possibleConstantsSplitted[taskID].resize(domain.tasks[taskID].variableSorts.size());
		for (size_t pc = 0; pc < possibleConstantsPerTask[taskID].size(); pc++){
			for (size_t varIDX = 0; varIDX < domain.tasks[taskID].variableSorts.size(); varIDX++){
				for (int e : possibleConstantsPerTask[taskID][pc][varIDX])
					possibleConstantsSplitted[taskID][varIDX][e].push_back(pc);
			}
		}
	}

	
	possibleConstantsPerMethodSplitted.resize(domain.decompositionMethods.size());
	for (size_t methodID = 0; methodID < domain.decompositionMethods.size(); methodID++){
		possibleConstantsPerMethodSplitted[methodID].resize(domain.decompositionMethods[methodID].variableSorts.size());
		
		for (size_t pc = 0; pc < possibleConstantsPerMethod[methodID].size(); pc++){
			for (size_t varIDX = 0; varIDX < domain.decompositionMethods[methodID].variableSorts.size(); varIDX++){
				for (int e : possibleConstantsPerMethod[methodID][pc][varIDX])
					possibleConstantsPerMethodSplitted[methodID][varIDX][e].push_back(pc);
			}
		}
	}
}

void HierarchyTyping::taskDfs (const Domain & domain, const Problem & problem, bool withStaticPreconditionChecking, const std::vector<bool> & staticPredicates, std::vector<std::vector<std::map<int,std::vector<int>>>> & factsPerPredicate, size_t taskNo, PossibleConstants possibleConstants)
{
	const Task & task = domain.tasks[taskNo];

	// Stop recursion if we already found this set of possible constants
	for (const auto & visitedConstants : possibleConstantsPerTask[taskNo])
	{
		assert (visitedConstants.size () == task.variableSorts.size ());

		bool visited = true;
		for (size_t varIdx = 0; varIdx < task.variableSorts.size (); ++varIdx)
		{
			if (!std::includes (visitedConstants[varIdx].begin (), visitedConstants[varIdx].end (), possibleConstants[varIdx].begin (), possibleConstants[varIdx].end ()))
			{
				visited = false;
				break;
			}
		}

		if (visited){
			DEBUG(std::cout << "Already visited" << std::endl);
			return;
		}
	}
	DEBUG(
		std::cout << "Adding Hierarchy Typing for " << taskNo << " " << domain.tasks[taskNo].name;
	   	std::cout << "[";
	   	bool first = true;
		for (auto p : possibleConstants){
			if (!first) std::cout << ",";
			std::cout << "{";
	   		bool ffirst = true;
			for (auto v : p){
				if (!ffirst) std::cout << ",";
				std::cout << domain.constants[v];
				ffirst = false;	
			}
			std::cout << "}";
			first = false;
		}	
		std::cout << "]";
		std::cout << std::endl;
			);
	
	possibleConstantsPerTask[taskNo].push_back (possibleConstants);

	for (int methodNo : task.decompositionMethods)
	{
		const DecompositionMethod & method = domain.decompositionMethods[methodNo];
		assert (task.variableSorts.size () == method.taskParameters.size ());

		// Determine possible constants for this method
		PossibleConstants possibleMethodConstants (method.variableSorts.size ());
		for (size_t methodVarIdx = 0; methodVarIdx < method.variableSorts.size (); ++methodVarIdx)
		{
			// Initially, we can use all constants from the method variable's sort.
			int sort = method.variableSorts[methodVarIdx];
			possibleMethodConstants[methodVarIdx] = domain.sorts[sort].members;
		}
		for (size_t taskVarIdx = 0; taskVarIdx < method.taskParameters.size (); ++taskVarIdx)
		{
			// For method variables that correspond to task variables, we intersect the possible constants.
			int methodVarIdx = method.taskParameters[taskVarIdx];
			possibleMethodConstants[methodVarIdx] = intersect (possibleMethodConstants[methodVarIdx], possibleConstants[taskVarIdx]);
		}
		applyConstraints (possibleMethodConstants, method.variableConstraints);


		// checking static preconditions of subtasks
		// TODO optimise this ordering ... start with subtasks that are likely to prune something
		// TODO also prefer preconditions that are likely to prune something
		if (withStaticPreconditionChecking) for (const auto & subtask : method.subtasks)
		{
			// can only check preconditions for primitive tasks
			if (subtask.taskNo >= domain.nPrimitiveTasks) continue;

			PossibleConstants possibleSubtaskConstants (subtask.arguments.size ());
			for (size_t subtaskVarIdx = 0; subtaskVarIdx < subtask.arguments.size (); ++subtaskVarIdx)
			{
				int methodVarIdx = subtask.arguments[subtaskVarIdx];
				possibleSubtaskConstants[subtaskVarIdx] = possibleMethodConstants[methodVarIdx];
			}

			for (size_t precID = 0; precID < domain.tasks[subtask.taskNo].preconditions.size(); precID++){
				if (!staticPredicates[domain.tasks[subtask.taskNo].preconditions[precID].predicateNo])
					continue;
				const int & predicate = domain.tasks[subtask.taskNo].preconditions[precID].predicateNo;
				const std::vector<int> & arguments = domain.tasks[subtask.taskNo].preconditions[precID].arguments;
				
				if (arguments.size() == 0) continue; // too buggy
				
				DEBUG(
				   	std::cout << "Subtask " << subtask.taskNo << " " << domain.tasks[subtask.taskNo].name << " has a static precondition on predicate " << predicate << " " << domain.predicates[predicate].name << std::endl;
				);

				// we have a static precondition, so we can prune along it
				PossibleConstants possiblePreconditionConstants (arguments.size());
				for (size_t predicateVarIdx = 0; predicateVarIdx < arguments.size(); predicateVarIdx++){
					int taskVarIndex = arguments[predicateVarIdx];
					possiblePreconditionConstants[predicateVarIdx] = possibleSubtaskConstants[taskVarIndex];
				}
				
				DEBUG(
					std::cout << "starting with ";
				   	bool first = true;
					for (auto p : possiblePreconditionConstants){
						if (!first) std::cout << ",";
						std::cout << "{";
				   		bool ffirst = true;
						for (auto v : p){
							if (!ffirst) std::cout << ",";
							std::cout << domain.constants[v];
							ffirst = false;	
						}
						std::cout << "}";
						first = false;
					}	
					std::cout << std::endl;
						);
	
				// let's check whether we violate something
				PossibleConstants newPossiblePreconditionConstants (arguments.size());
				
				// only do facts that are actually useful
				int smallestNumberOfInstances = 0x3f3f3f3f;
				int indexOfSmallest = 0x3f3f3f3f;
				for (size_t predicateVarIdx = 0; predicateVarIdx < arguments.size(); predicateVarIdx++){
					int size = possiblePreconditionConstants[predicateVarIdx].size();

					if (size < smallestNumberOfInstances){
						smallestNumberOfInstances = size;
						indexOfSmallest = predicateVarIdx;
					}
				}

				assert(smallestNumberOfInstances != 0x3f3f3f3f);

				for (const int & val : possiblePreconditionConstants[indexOfSmallest])
					for (int factNo : factsPerPredicate[predicate][indexOfSmallest][val]){
					  	const Fact & f = problem.init[factNo];
						// check whether all are ok
						bool possible = true;
						for (size_t predicateVarIdx = 0; predicateVarIdx < arguments.size(); predicateVarIdx++)
							if (possiblePreconditionConstants[predicateVarIdx].count(f.arguments[predicateVarIdx]) == 0){
								possible = false;
								break;
							}
						
						if (!possible) continue;
						
						for (size_t predicateVarIdx = 0; predicateVarIdx < arguments.size(); predicateVarIdx++)
							newPossiblePreconditionConstants[predicateVarIdx].insert(f.arguments[predicateVarIdx]);
					}
					
				DEBUG(
					std::cout << "Pruned arguments to ";
				   	bool first = true;
					for (auto p : newPossiblePreconditionConstants){
						if (!first) std::cout << ",";
						std::cout << "{";
				   		bool ffirst = true;
						for (auto v : p){
							if (!ffirst) std::cout << ",";
							std::cout << domain.constants[v];
							ffirst = false;	
						}
						std::cout << "}";
						first = false;
					}	
					std::cout << std::endl;
						);

				// writing back the information to the overall arguments of the task
				for (size_t predicateVarIdx = 0; predicateVarIdx < arguments.size(); predicateVarIdx++){
					int taskVarIndex = arguments[predicateVarIdx];
	
					std::set<int> newConstants;
					for (int c : possibleSubtaskConstants[taskVarIndex])
						if (newPossiblePreconditionConstants[predicateVarIdx].count(c))
							newConstants.insert(c);
					
					DEBUG(if (newConstants.size() < possibleSubtaskConstants[taskVarIndex].size())
							std::cout << "Reducing size of TaskVar" << taskVarIndex << std::endl);
					possibleSubtaskConstants[taskVarIndex] = newConstants;
				}
			}
			
			// writing back to the method's constants
			for (size_t subtaskVarIdx = 0; subtaskVarIdx < subtask.arguments.size (); ++subtaskVarIdx)
			{
				int methodVarIdx = subtask.arguments[subtaskVarIdx];

				std::set<int> newConstants;
				for (int c : possibleMethodConstants[methodVarIdx])
					if (possibleSubtaskConstants[subtaskVarIdx].count(c))
					   newConstants.insert(c);
				possibleMethodConstants[methodVarIdx] = newConstants;
			}
		}
	


		// If we have no valid assignment for a variable, we cannot instantiate this method.
		if (std::any_of (possibleMethodConstants.begin (), possibleMethodConstants.end (), [](const auto & possibleValues) { return possibleValues.size () == 0; }))
			continue;

		possibleConstantsPerMethod[methodNo].push_back (possibleMethodConstants);


		for (const auto & subtask : method.subtasks)
		{
			assert (subtask.arguments.size () == domain.tasks[subtask.taskNo].variableSorts.size ());

			PossibleConstants possibleSubtaskConstants (subtask.arguments.size ());
			for (size_t subtaskVarIdx = 0; subtaskVarIdx < subtask.arguments.size (); ++subtaskVarIdx)
			{
				int methodVarIdx = subtask.arguments[subtaskVarIdx];
				possibleSubtaskConstants[subtaskVarIdx] = possibleMethodConstants[methodVarIdx];
			}
			applyConstraints (possibleSubtaskConstants, domain.tasks[subtask.taskNo].variableConstraints);

			DEBUG(
				std::cout << "Coming from " << taskNo << " " << domain.tasks[taskNo].name;
				std::cout << " via the method " << methodNo << " " << method.name;
			   	std::cout << " to " << subtask.taskNo << " " << domain.tasks[subtask.taskNo].name << std::endl;
			);
			taskDfs (domain, problem, withStaticPreconditionChecking, staticPredicates, factsPerPredicate, subtask.taskNo, possibleSubtaskConstants);
		}
	}
}

static bool isAssignmentCompatibleSplitted (const std::vector<PossibleConstants> & allConstants, const std::vector<int> & actuallyPossibleConstants, const VariableAssignment & assignedVariables)
{
	for (const int & possibleID : actuallyPossibleConstants)
	{
		const auto & possibleConstants = allConstants[possibleID];
		bool valid = true;
		for (size_t varIdx = 0; varIdx < possibleConstants.size (); ++varIdx)
		{
			int varValue = assignedVariables[varIdx];
			if (assignedVariables.NOT_ASSIGNED != varValue && possibleConstants[varIdx].count (varValue) == 0)
			{
				valid = false;
				break;
			}
		}
		if (valid)
			return true;

	}
	return false;
}


static bool isAssignmentCompatible (const std::vector<PossibleConstants> & possibleConstants, const VariableAssignment & assignedVariables)
{
	for (const auto & possibleConstants : possibleConstants)
	{
		bool valid = true;
		for (size_t varIdx = 0; varIdx < possibleConstants.size (); ++varIdx)
		{
			int varValue = assignedVariables[varIdx];
			if (assignedVariables.NOT_ASSIGNED != varValue && possibleConstants[varIdx].count (varValue) == 0)
			{
				valid = false;
				break;
			}
		}
		if (valid)
			return true;

	}
	return false;
}

template<>
bool HierarchyTyping::isAssignmentCompatible<Task> (int taskNo, const VariableAssignment & assignedVariables) const
{
	if (domain->tasks[taskNo].isCompiledConditionalEffect) return true; // actions representing conditional effects will always be kept. Their main task already passed HT checking


	int best = -1;
	int bestSize = 0x3f3f3f3f;
	for (size_t varIdx = 0; varIdx < assignedVariables.assignments.size (); ++varIdx){
		int e = assignedVariables[varIdx]; 
		if (e == assignedVariables.NOT_ASSIGNED) continue;
		auto it = possibleConstantsSplitted[taskNo][varIdx].find(e);
		if (it == possibleConstantsSplitted[taskNo][varIdx].end()) return false;
		if (bestSize > it->second.size()){
			best = varIdx;
			bestSize = it->second.size();
		}
	}
	if (best != -1){
		int e = assignedVariables[best]; 
		return ::isAssignmentCompatibleSplitted(possibleConstantsPerTask[taskNo], possibleConstantsSplitted[taskNo][best].at(e), assignedVariables);
	}

	if (best == -1 && assignedVariables.assignments.size()) return true; // nothing constrained yet

	return ::isAssignmentCompatible (possibleConstantsPerTask[taskNo], assignedVariables);
}

template<>
bool HierarchyTyping::isAssignmentCompatible<DecompositionMethod> (int methodNo, const VariableAssignment & assignedVariables) const
{
	int best = -1;
	int bestSize = 0x3f3f3f3f;
	for (size_t varIdx = 0; varIdx < assignedVariables.assignments.size (); ++varIdx){
		int e = assignedVariables[varIdx]; 
		if (e == assignedVariables.NOT_ASSIGNED) continue;
		auto it = possibleConstantsPerMethodSplitted[methodNo][varIdx].find(e);
		if (it == possibleConstantsPerMethodSplitted[methodNo][varIdx].end()) return false;
		if (bestSize > it->second.size()){
			best = varIdx;
			bestSize = it->second.size();
		}
	}
	if (best != -1){
		int e = assignedVariables[best]; 
		return ::isAssignmentCompatibleSplitted(possibleConstantsPerMethod[methodNo], possibleConstantsPerMethodSplitted[methodNo][best].at(e), assignedVariables);
	}

	if (best == -1 && assignedVariables.assignments.size()) return true; // nothing constrained yet

	return ::isAssignmentCompatible (possibleConstantsPerMethod[methodNo], assignedVariables);
}
