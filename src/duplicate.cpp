#include <iostream>

#include "debug.h"
#include "duplicate.h"

void unify_duplicates(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		grounding_configuration & config	
		){
	if (!config.quietMode) std::cout << "Starting duplicate elimination." << std::endl;
	// try do find tasks with identical preconditions and effects
	std::map<std::tuple<std::vector<int>, std::vector<int>, std::vector<int>>, std::vector<int>> duplicateArtificial;
	std::map<std::tuple<std::vector<int>, std::vector<int>, std::vector<int>, std::string, std::vector<int>>, std::vector<int>> duplicateConcatinated;
	
	for (size_t tID = 0; tID < reachableTasks.size(); tID++){
		if (prunedTasks[tID]) continue;
		// don't do duplicate detection on abstract tasks
		if (reachableTasks[tID].taskNo >= domain.nPrimitiveTasks) continue;
		
		// check whether they are actually eligible for merging (only those that start with an underscore or a paragraph)
		if (domain.tasks[reachableTasks[tID].taskNo].name[0] != '_' && domain.tasks[reachableTasks[tID].taskNo].name[0] != '%') continue;

		std::vector<int> pre;
		std::vector<int> add;
		std::vector<int> del;

		for (int x : reachableTasks[tID].groundedPreconditions) if (!prunedFacts[x]) pre.push_back(x);
		for (int x : reachableTasks[tID].groundedAddEffects) 	if (!prunedFacts[x]) add.push_back(x);
		for (int x : reachableTasks[tID].groundedDelEffects) 	if (!prunedFacts[x]) del.push_back(x);
		
		if (domain.tasks[reachableTasks[tID].taskNo].name[0] == '_'){
			duplicateArtificial[std::make_tuple(pre,add,del)].push_back(tID);
		} else if (domain.tasks[reachableTasks[tID].taskNo].name[0] == '%'){
			duplicateConcatinated[std::make_tuple(pre,add,del,domain.tasks[reachableTasks[tID].taskNo].name,reachableTasks[tID].arguments)].push_back(tID);
		}
	}
	if (!config.quietMode) std::cout << "Data structure build." << std::endl;


	std::map<int,int> taskReplacement;

	for (auto & entry : duplicateArtificial){
		if (entry.second.size() == 1) continue;

		DEBUG(std::cout << "Found artificial action duplicates:";
				for (int t : entry.second) std::cout << " " << t;
				std::cout << std::endl);

		int representative = entry.second[0];

		// remove the others
		for (size_t i = 1; i < entry.second.size(); i++){
			taskReplacement[entry.second[i]] = representative;
			prunedTasks[entry.second[i]] = true;
		}
	}

	for (auto & entry : duplicateConcatinated){
		if (entry.second.size() == 1) continue;

		DEBUG(std::cout << "Found concatenation action duplicates:";
				for (int t : entry.second) std::cout << " " << t;
				std::cout << std::endl);

		int representative = entry.second[0];

		// remove the others
		for (size_t i = 1; i < entry.second.size(); i++){
			taskReplacement[entry.second[i]] = representative;
			prunedTasks[entry.second[i]] = true;
		}
	}
	if (!config.quietMode) std::cout << taskReplacement.size() << " duplicates found." << std::endl;

	// perform the actual replacement (in methods)
	for (size_t mID = 0; mID < reachableMethods.size(); mID++){
		if (prunedMethods[mID]) continue;
		for (size_t sub = 0; sub < reachableMethods[mID].groundedPreconditions.size(); sub++){
			auto it = taskReplacement.find(reachableMethods[mID].groundedPreconditions[sub]);
			if (it == taskReplacement.end()) continue;

			reachableMethods[mID].groundedPreconditions[sub] = it->second;
		}
	}
	
	if (!config.quietMode) std::cout << "Duplicates replaced in methods." << std::endl;
}

