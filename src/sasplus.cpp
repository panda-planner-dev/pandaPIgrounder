#include "sasplus.h"
#include <unordered_set>

void write_sasplus(std::ostream & sout, const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		grounding_configuration & config){

	// mandated output ..
	sout << "begin_version" << std::endl << "3" << std::endl << "end_version" << std::endl;
	sout << "begin_metric" << std::endl << "1" << std::endl << "end_metric" << std::endl;

	// determine the number of unpruned facts
	int unprunedFacts = 0;
	for (bool x : prunedFacts) if (!x) unprunedFacts++;
	sout << unprunedFacts + (problem.initialAbstractTask == -1? 0 : 1) << std::endl;

	// contains mapping from output IDs to internal IDS
	std::vector<int> factOutput;
	std::vector<int> factIDtoOutputOutput;
	std::set<Fact> outputFactsSet;
	for(size_t factID = 0; factID < reachableFacts.size(); factID++){
		if (prunedFacts[factID]) {
			factIDtoOutputOutput.push_back(-1);
			continue;
		}
		int factOut = factOutput.size();
		factOutput.push_back(factID);
		factIDtoOutputOutput.push_back(factOut);

		Fact & fact = reachableFacts[factID];
		outputFactsSet.insert(fact);

		sout << "begin_variable" << std::endl << "var" << factOut << std::endl << "-1" << std::endl << "2" << std::endl;
		std::string factName = domain.predicates[fact.predicateNo].name + "[";
		for (unsigned int i = 0; i < fact.arguments.size(); i++){
			if (i) factName += ",";
			factName += domain.constants[fact.arguments[i]];
		}
		factName += "]";

		sout << "Atom " << factName << std::endl;
		sout << "NotAtom " << factName << std::endl;
		sout << "end_variable" << std::endl;
	}

	if (problem.initialAbstractTask != -1){
		sout << "begin_variable" << std::endl << "fakeGoal" << std::endl << "-1" << std::endl << "2" << std::endl;
		sout << "GOAL" << std::endl << "NOT GOAL" << std::endl;
		sout << "end_variable" << std::endl;
	}


	sout << "0" << std::endl; // I don't know of any non-trivial mutexes

	std::set<Fact> initFacts (problem.init.begin(), problem.init.end());
	sout << "begin_state" << std::endl;
	for (int & factID : factOutput){
		Fact & fact = reachableFacts[factID];
		auto initFactIterator = initFacts.find(fact);
		if (initFactIterator != initFacts.end())
			sout << 0 << std::endl;
		else
			sout << 1 << std::endl;
	}
	if (problem.initialAbstractTask != -1) sout << 1 << std::endl;
	sout << "end_state" << std::endl;


	std::vector<int> goalFacts;
	for (const Fact & f : problem.goal){
		auto it = outputFactsSet.find(f);
		if (it == outputFactsSet.end()) continue; // might be unsolvable, but we shall detect this at another place.
		if (prunedFacts[it->groundedNo]) continue; // same as above

		goalFacts.push_back(factIDtoOutputOutput[it->groundedNo]);
	}
	
	if (problem.initialAbstractTask != -1) goalFacts.push_back(unprunedFacts);
	sout << "begin_goal" << std::endl << goalFacts.size() << std::endl;
	for (int gf : goalFacts) sout << gf << " " << 0 << std::endl;
	sout << "end_goal" << std::endl;


	int primitiveTasks = 0;
	for(size_t i = 0; i < reachableTasks.size(); i++)
		if (! prunedTasks[i] && reachableTasks[i].taskNo < domain.nPrimitiveTasks)
				primitiveTasks++;

	sout << primitiveTasks << std::endl;


	std::map<Fact,int> init_functions_map;
	for (auto & init_function_literal : problem.init_functions){
		init_functions_map[init_function_literal.first] = init_function_literal.second;
	}
	
	for(size_t taskID = 0; taskID < reachableTasks.size(); taskID++) if (! prunedTasks[taskID] && reachableTasks[taskID].taskNo < domain.nPrimitiveTasks){
		sout << "begin_operator" << std::endl;
		GroundedTask & task = reachableTasks[taskID];

		sout << domain.tasks[task.taskNo].name << "[";
		// only output the original variables
		for (unsigned int i = 0; i < domain.tasks[task.taskNo].number_of_original_variables; i++){
			if (i) sout << ",";
			sout << domain.constants[task.arguments[i]];
		}
		sout << "]" << std::endl;

		// determine the prevail  

		std::unordered_set<int> pre,add,del;
		for (int & prec : task.groundedPreconditions)
			if (!prunedFacts[prec])
				pre.insert(factIDtoOutputOutput[prec]);
		
		for (int & addf : task.groundedAddEffects)
			if (!prunedFacts[addf])
				add.insert(factIDtoOutputOutput[addf]);
		
		for (int & delf : task.groundedDelEffects)
			if (!prunedFacts[delf])
				del.insert(factIDtoOutputOutput[delf]);

		std::unordered_set<int> prevail;
		for (const int & p : pre) if (!del.count(p)) prevail.insert(p);



		// output operator
		sout << prevail.size() << std::endl;
		for (const int & p : prevail) sout << p << " " << 0 << std::endl;

		sout << add.size() + del.size() + (problem.initialAbstractTask == -1? 0 : 1) << std::endl;
		for (const int & x : add) sout << 0 << " " << x << " " << -1 << " " << 0 << std::endl;
		for (const int & x : del) sout << 0 << " " << x << " " << (pre.count(x)?0:-1) << " " << 1 << std::endl;
		if (problem.initialAbstractTask != -1) sout << 0 << " " << unprunedFacts << " " << -1 << " " << 0 << std::endl;


		int costs = domain.tasks[task.taskNo].computeGroundCost(task,init_functions_map);
		sout << costs << std::endl;
		sout << "end_operator" << std::endl;
	}
}
