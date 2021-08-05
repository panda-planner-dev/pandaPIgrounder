#include <unistd.h>
#include <iostream>
#include <cassert>
#include <algorithm>


#include "util.h"
#include "postprocessing.h"
#include "debug.h"



void sortSubtasksOfMethodsTopologically(const Domain & domain,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		std::vector<GroundedMethod> & inputMethodsGroundedTdg){
	for (GroundedMethod & method : inputMethodsGroundedTdg){
		if (prunedMethods[method.groundedNo]) continue;
		
		// find a topological ordering of the subtasks
		std::vector<std::vector<int>> adj(method.groundedPreconditions.size());
		
		auto orderings = domain.decompositionMethods[method.methodNo].orderingConstraints;
		for (std::pair<int,int> ordering : orderings)
			adj[ordering.first].push_back(ordering.second);

		topsort(adj, method.preconditionOrdering);

	}
}


void applyEffectPriority(const Domain & domain,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<GroundedTask> & inputTasksGroundedPg,
		std::vector<Fact> & inputFactsGroundedPg){

	// gather conditional effect actions
	std::map<int,GroundedTask> ce_effects;
	for (GroundedTask & task : inputTasksGroundedPg){
		if (!domain.tasks[task.taskNo].isCompiledConditionalEffect) continue;
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;

		int guardID = -1;
		for (int & prec : task.groundedPreconditions)
			if (domain.predicates[inputFactsGroundedPg[prec].predicateNo].guard_for_conditional_effect){
				guardID = prec;
				break;
			}

		if (ce_effects.count(guardID)){
			std::cerr << "Multiple assigned conditional effect groundings. I thought this cannot happen ..." << std::endl;
			exit(-1);
		}

		ce_effects[guardID] = task;
	}




	for (GroundedTask & task : inputTasksGroundedPg){
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;

		std::set<int> addSet; for (int & add : task.groundedAddEffects) addSet.insert(add);

		// look for del effects that are also add effects
		std::set<int> addToRemove;
		std::set<int> delToRemove;
		for (int & del : task.groundedDelEffects)
			if (addSet.count(del)){
				// edge case, if this is a negated original predicate, then the del effect takes precedence
				Fact & fact = inputFactsGroundedPg[del];
				if (domain.predicates[fact.predicateNo].name[0] != '-')
					delToRemove.insert(del);
				else
					addToRemove.insert(del);
			}

		if (addToRemove.size()){
			std::vector<int> newAdd;
			for (int & add : task.groundedAddEffects)
				if (! addToRemove.count(add))
					newAdd.push_back(add);
			task.groundedAddEffects = newAdd;
		}

		if (delToRemove.size()){
			std::vector<int> newDel;
			for (int & del : task.groundedDelEffects)
				if (! delToRemove.count(del))
					newDel.push_back(del);
			task.groundedDelEffects = newDel;
		}

		addSet.clear(); for (int & add : task.groundedAddEffects) addSet.insert(add);
		std::set<int> delSet; for (int & del : task.groundedDelEffects) delSet.insert(del);


		// handle conditional effects correctly

		// first find all guard effects of this action
		std::vector<int> ce_guards;
		for (int & add : task.groundedAddEffects)
			if (domain.predicates[inputFactsGroundedPg[add].predicateNo].guard_for_conditional_effect)
				ce_guards.push_back(add);



		std::map<int,std::pair<std::vector<int>,std::vector<int>>> ces; // per effect ID (ground number), a list of adding and a list of deleting

		// compute conditional effects
		for (int guard : ce_guards){
			if (!ce_effects.count(guard)) continue; // CE condition might be unreachable
			GroundedTask ce_task = ce_effects[guard];
			
			// these cannot have effect precedence, as they contain only a single effect, i.e. it is fine to handle them while applying add precedence
			int effectID; bool isAdd;
			if (ce_task.groundedAddEffects.size()){
				assert(ce_task.groundedDelEffects.size() == 0);
				assert(ce_task.groundedAddEffects.size() == 1);
				effectID = ce_task.groundedAddEffects[0];
				isAdd = true;
			} else {
				assert(ce_task.groundedDelEffects.size() == 1);
				assert(ce_task.groundedAddEffects.size() == 0);
				effectID = ce_task.groundedDelEffects[0];
				isAdd = false;
			}

			if (prunedFacts[effectID]) continue; // this effect is not necessary

			if (isAdd)
				ces[effectID].first.push_back(ce_task.groundedNo);
			else
				ces[effectID].second.push_back(ce_task.groundedNo);
		}
		
		DEBUG(std::cout << "Prioritizing conditional effects of: " << domain.tasks[task.taskNo].name << std::endl);

		// look at all possible effects
		for (auto [factID,adddel] : ces){
			auto adds = adddel.first;
			auto dels = adddel.second;
			
			DEBUG(std::cout << "Effect: " << factID << " " << domain.predicates[inputFactsGroundedPg[factID].predicateNo].name << std::endl);

			// precedence with fixed effect
			if (addSet.count(factID)){
				// add effects are useless
				for (int add : adds) prunedTasks[add] = true;

				// add may precedence over del
				
				// for edge case, check whether this is an add effect
				Fact & fact = inputFactsGroundedPg[factID];
				if (domain.predicates[fact.predicateNo].name[0] != '-'){
					for (int del : dels) prunedTasks[del] = true;
				} else {
					// for this, the deletes would take precedence, but I cant write this to the output
					for (int del : dels){
						if (prunedTasks[del]) continue;
						std::cerr << "Unpruned conditional delete effect on fact " << factID << " with is negative, but also necessarily added." << std::endl;
						std::cerr << "This is not supported. You need to rewrite your domain s.t. this does not occur or turn off the -k flag of the parser." << std::endl;
						exit(-1);
					}
				}
			}

			// precedence with fixed effect
			if (delSet.count(factID)){
				// del effects are useless
				for (int del : dels) prunedTasks[del] = true;

				// for edge case, check whether this is an add effect
				Fact & fact = inputFactsGroundedPg[factID];
				if (domain.predicates[fact.predicateNo].name[0] != '-'){
					// for this, the adds would take precedence, but I cant write this to the output
					for (int add : adds){
						if (prunedTasks[add]) continue;
						std::cerr << "Unpruned conditional add effect on fact " << factID << " with is positive, but also necessarily deleted." << std::endl;
						std::cerr << "This is not supported. You need to rewrite your domain s.t. this does not occur or turn off the -k flag of the parser." << std::endl;
						exit(-1);
					}
				} else {
					for (int add : adds) prunedTasks[add] = true;
				}
				
			}


			for (int add : adds) {
				if (prunedTasks[add]) continue;
				for (int del : dels){
					if (prunedTasks[del]) continue;

					DEBUG(std::cout << "ADD: " << add << " DEL: " << del << std::endl);
					
					// check whether they have the same precondition
					// get cleared list of preconditions of the add
					std::vector<int> addP;
			   		for (const int & a : inputTasksGroundedPg[add].groundedPreconditions)
						if (!domain.predicates[inputFactsGroundedPg[a].predicateNo].guard_for_conditional_effect)
							addP.push_back(a); // don't add the guard predicate
					sort(addP.begin(), addP.end());
					// and the delete	
					std::vector<int> delP;
					for (const int & d : inputTasksGroundedPg[del].groundedPreconditions)
						if (!domain.predicates[inputFactsGroundedPg[d].predicateNo].guard_for_conditional_effect)
							delP.push_back(d); // don't add the guard predicate
					sort(delP.begin(), delP.end());
					
					
					DEBUG(std::cout << "ADD prec:"; for (int x : addP) std::cout << " " << x; std::cout << std::endl);
					DEBUG(std::cout << "DEL prec:"; for (int x : delP) std::cout << " " << x; std::cout << std::endl);

					if (addP.size() != delP.size()) continue;
					bool same = true;
					for (size_t i = 0; i < addP.size(); i++) if (addP[i] != delP[i]) {same = false; break;}
					if (!same) continue;


					// they are the same, so one must be removed
		
					// edge case, if this is a negated original predicate, then the del effect takes precedence
					Fact & fact = inputFactsGroundedPg[factID];
					if (domain.predicates[fact.predicateNo].name[0] != '-'){
						prunedTasks[del] = true;
						DEBUG(std::cout << "Pruning del action " << del << std::endl);
					} else {
						prunedTasks[add] = true;
						DEBUG(std::cout << "Pruning add action " << add << std::endl);
					}
				}
			}
		}
	}
}


void removeUnnecessaryFacts(const Domain & domain,
		const Problem & problem,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<GroundedTask> & inputTasksGroundedPg,
		std::vector<Fact> & inputFactsGroundedPg){

	std::set<Fact> reachableFacts(inputFactsGroundedPg.begin(), inputFactsGroundedPg.end());
	//

	// find facts that are static
	// first determine their initial truth value
	std::vector<bool> initialTruth(prunedFacts.size());
	// all facts in the initial state are initially true
	for (const Fact & f : problem.init)
		initialTruth[reachableFacts.find(f)->groundedNo] = true;

	// check all non-pruned action's effects
	std::vector<bool> truthChanges (prunedFacts.size());
	for (GroundedTask & task : inputTasksGroundedPg){
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;
		// iterate over add and del effects
		for (int & add : task.groundedAddEffects)
			if (!initialTruth[add]) // if an actions adds this, but it is not initially true, it might be added
				truthChanges[add] = true;
			
		for (int & del : task.groundedDelEffects)
			if (initialTruth[del]) // opposite for a del
				truthChanges[del] = true;
	}

	// look out for facts whose truth never changes
	for (int f = 0; f < initialTruth.size(); f++)
		if (!truthChanges[f]){
			DEBUG(
			Fact & fact = inputFactsGroundedPg[f];
			std::cout << "static predicate " << domain.predicates[fact.predicateNo].name << "[";
			for (unsigned int i = 0; i < fact.arguments.size(); i++){
				if (i) std::cout << ",";
				std::cout << domain.constants[fact.arguments[i]];
			}
			std::cout << "]" << std::endl;
		
			for (const Fact & gf : problem.goal){
				auto it = reachableFacts.find(gf);
				if (it != reachableFacts.end()){
					if (f == it->groundedNo){
						std::cout << "Deleting goal fact, in init " << initialTruth[f] << std::endl;
					}
				}
			});

			// prune the fact that does not change its truth value
			prunedFacts[f] = true;
		}
	
	// look for facts that to not occur in preconditions. They can be removed as well
	std::vector<bool> occuringInPrecondition (prunedFacts.size());
	for (GroundedTask & task : inputTasksGroundedPg)
		for (int & pre : task.groundedPreconditions)
			occuringInPrecondition[pre] = true;
	// facts in the goal may also not be removed
	for (const Fact & f : problem.goal){
		auto it = reachableFacts.find(f);
		if (it == reachableFacts.end()){
			// TODO detect this earlier and do something intelligent
			std::cerr << "Goal is unreachable ..." << std::endl;
			_exit(0);
		}
		occuringInPrecondition[it->groundedNo] = true;
	}

	// remove facts that are not contained in preconditions
	for (int f = 0; f < occuringInPrecondition.size(); f++)
		if (!occuringInPrecondition[f]){
			DEBUG(
			Fact & fact = inputFactsGroundedPg[f];
			std::cout << "no precondition predicate " << domain.predicates[fact.predicateNo].name << "[";
			for (unsigned int i = 0; i < fact.arguments.size(); i++){
				if (i) std::cout << ",";
				std::cout << domain.constants[fact.arguments[i]];
			}
			std::cout << "]" << std::endl;

			for (const Fact & gf : problem.goal){
				auto it = reachableFacts.find(gf);
				if (it != reachableFacts.end()){
					if (f == it->groundedNo){
						std::cout << "Deleting goal fact, in init " << initialTruth[f] << std::endl;
					}
				}
			});

			// prune the fact that does not change its truth value
			prunedFacts[f] = true;
		}
}

void expandAbstractTasksWithSingleMethod(const Domain & domain,
		const Problem & problem,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		std::vector<GroundedTask> & inputTasksGroundedPg,
		std::vector<GroundedMethod> & inputMethodsGroundedTdg,
		bool keepTwoRegularisation){

	std::vector<std::set<int>> taskToMethodsTheyAreContainedIn (inputTasksGroundedPg.size());
	for (auto & method : inputMethodsGroundedTdg){
		if (prunedMethods[method.groundedNo]) continue;
		for (size_t subTaskIdx = 0; subTaskIdx < method.groundedPreconditions.size(); subTaskIdx++)
			taskToMethodsTheyAreContainedIn[method.groundedPreconditions[subTaskIdx]].insert(method.groundedNo);
	}
	
	// may need to repeat due to empty methods hat might create new unit methods
	bool emptyExpanded = true;
	while (emptyExpanded) {
		emptyExpanded = false;
		for (auto & groundedTask : inputTasksGroundedPg){
			if (prunedTasks[groundedTask.groundedNo]) continue;
			if (groundedTask.taskNo < domain.nPrimitiveTasks) continue;
			// don't compactify the top method
			if (groundedTask.taskNo == problem.initialAbstractTask) continue;
			
			int applicableIndex = -1;
			for (auto & groundedMethodIdx : groundedTask.groundedDecompositionMethods)
			{
				if (prunedMethods[groundedMethodIdx])
					continue;
				if (applicableIndex != -1) {
					applicableIndex = -2;
					break;
				}
				applicableIndex = groundedMethodIdx;
			}
			// it can't be -1, else the TDG would have eliminated it
			if (applicableIndex == -2) continue;
			assert(applicableIndex != -1);

			GroundedMethod & unitGroundedMethod = inputMethodsGroundedTdg[applicableIndex];
			DecompositionMethod unitLiftedMethod = domain.decompositionMethods[unitGroundedMethod.methodNo];

			
			int maxSizeofContained = 0;
			for (const int & method : taskToMethodsTheyAreContainedIn[groundedTask.groundedNo]){
				if (prunedMethods[method]) continue;
				GroundedMethod & groundedMethod = inputMethodsGroundedTdg[method];
				if (groundedMethod.groundedPreconditions.size() > maxSizeofContained) maxSizeofContained = groundedMethod.groundedPreconditions.size();
			}
			
			if (keepTwoRegularisation && unitGroundedMethod.groundedPreconditions.size() >= 2 && maxSizeofContained > 1)
				continue;

			// this method is now pruned ...
			prunedMethods[applicableIndex] = true;
			prunedTasks[groundedTask.groundedNo] = true;
	
			std::string decomposedTaskName = domain.tasks[groundedTask.taskNo].name + "[";
			for (size_t i = 0; i < groundedTask.arguments.size(); i++){
				if (i) decomposedTaskName += ",";
				decomposedTaskName += domain.constants[groundedTask.arguments[i]];
			}
			decomposedTaskName += "]";
	
			// apply this method in all methods it is occurring
			DEBUG( std::cerr << "Abstract task " << decomposedTaskName << " (" << groundedTask.groundedNo << ") has only a single method" << std::endl);
			for (const int & method : taskToMethodsTheyAreContainedIn[groundedTask.groundedNo]){
				if (prunedMethods[method]) continue;
				// copy the lifted method
				GroundedMethod & groundedMethod = inputMethodsGroundedTdg[method];
				DecompositionMethod liftedMethod = domain.decompositionMethods[groundedMethod.methodNo];
				
				DEBUG( std::cerr << "expanding in method " << liftedMethod.name << " (" << method << ")" << std::endl);
				
				while (true){
					bool found = false;
					for (size_t subTaskIdx = 0; subTaskIdx < liftedMethod.subtasks.size(); subTaskIdx++){
						DEBUG( std::cerr << "Checking  #" << subTaskIdx << ": " << groundedMethod.groundedPreconditions[subTaskIdx] << " == " << groundedTask.groundedNo << "?" << std::endl);
						if (groundedMethod.groundedPreconditions[subTaskIdx] == groundedTask.groundedNo){
							found = true;
							DEBUG( std::cerr << "Yes, so expand it" << std::endl);
	
							std::vector<std::pair<int,int>> orderPertainingToThisTask;
							std::vector<std::pair<int,int>> orderNotPertainingToThisTask;
							for(auto order : liftedMethod.orderingConstraints)
								if (order.first == subTaskIdx || order.second == subTaskIdx)
									orderPertainingToThisTask.push_back(order);
								else 
									orderNotPertainingToThisTask.push_back(order);
		
							
							std::vector<int> idmapping;
							int positionOfExpanded = -1;
	
							// if the method we have to apply is empty
							if (unitGroundedMethod.groundedPreconditions.size() == 0){
								DEBUG( std::cerr << "Applied method is empty." << std::endl);
								emptyExpanded = true;
								groundedMethod.groundedPreconditions.erase(groundedMethod.groundedPreconditions.begin() + subTaskIdx);
								liftedMethod.subtasks.erase(liftedMethod.subtasks.begin() + subTaskIdx);
								// adapt the ordering of the subtasks accordingly

								std::vector<int> newOrder;
								for (size_t i = 0; i < groundedMethod.preconditionOrdering.size(); i++){
									if (groundedMethod.preconditionOrdering[i] == subTaskIdx){
										positionOfExpanded = i;
									} else {
										bool afterDeleted = groundedMethod.preconditionOrdering[i] > subTaskIdx;
										newOrder.push_back(groundedMethod.preconditionOrdering[i] - (afterDeleted?1:0));
										idmapping.push_back(i);
									}
								}

								groundedMethod.preconditionOrdering = newOrder;

								// orderings that were transitively induced using the removed task
								for (auto a : orderPertainingToThisTask) {
									if (a.second != subTaskIdx) continue;
									for (auto b : orderPertainingToThisTask) {
										if (b.first != subTaskIdx) continue;
										orderNotPertainingToThisTask.push_back(std::make_pair(a.first,b.second));
									}
								}
								liftedMethod.orderingConstraints.clear();
								for (auto order : orderNotPertainingToThisTask){
									if (order.first > subTaskIdx) order.first--;
									if (order.second > subTaskIdx) order.second--;
									liftedMethod.orderingConstraints.push_back(order);
								}
							} else {
								DEBUG( std::cerr << "Applied method is not empty." << std::endl);
								// set first subtask and add the rest
								groundedMethod.groundedPreconditions[subTaskIdx] = unitGroundedMethod.groundedPreconditions[0];
								int originalMethodSize = groundedMethod.groundedPreconditions.size();
								for (size_t i = 1; i < unitGroundedMethod.groundedPreconditions.size(); i++){
									for (auto order : orderPertainingToThisTask)
										if (order.first == subTaskIdx)
											liftedMethod.orderingConstraints.push_back(std::make_pair(groundedMethod.groundedPreconditions.size(), order.second));
										else 
											liftedMethod.orderingConstraints.push_back(std::make_pair(order.first, groundedMethod.groundedPreconditions.size())); 
									
									groundedMethod.groundedPreconditions.push_back(unitGroundedMethod.groundedPreconditions[i]);
									liftedMethod.subtasks.push_back(liftedMethod.subtasks[subTaskIdx]);
									// add to the name of the method what we have done
								}

								// update the ordering
								std::vector<int> newOrdering;
								for (size_t i = 0; i < groundedMethod.preconditionOrdering.size(); i++){
									if (groundedMethod.preconditionOrdering[i] == subTaskIdx){
										positionOfExpanded = i;
										// insert the ordering of the unit method here
									
										for (size_t j = 0; j < unitGroundedMethod.preconditionOrdering.size(); j++){
											int unitTaskID = unitGroundedMethod.preconditionOrdering[j];
											if (unitTaskID == 0){
												// the re-used task
												newOrdering.push_back(groundedMethod.preconditionOrdering[i]);
											} else {
												newOrdering.push_back(groundedMethod.preconditionOrdering.size() + unitTaskID - 1);
											}
											idmapping.push_back(-j-1);
										}

										//
									} else {
										newOrdering.push_back(groundedMethod.preconditionOrdering[i]);
										idmapping.push_back(i);
									}
								}
								groundedMethod.preconditionOrdering = newOrdering;


								for (auto order : unitLiftedMethod.orderingConstraints) {
									if (order.first == 0) // the replaced task
										liftedMethod.orderingConstraints.push_back(std::make_pair(subTaskIdx, order.second - 1 + originalMethodSize));
									else if (order.second == 0) // the replaced task
										liftedMethod.orderingConstraints.push_back(std::make_pair(order.first - 1 + originalMethodSize, subTaskIdx)); 
									else
										liftedMethod.orderingConstraints.push_back(std::make_pair(order.first - 1 + originalMethodSize, order.second - 1 + originalMethodSize)); 
								}
	
	
								// update table accordingly as new tasks are now contained in this method 
								for (size_t i = 0; i < unitGroundedMethod.groundedPreconditions.size(); i++){
									taskToMethodsTheyAreContainedIn[unitGroundedMethod.groundedPreconditions[i]].insert(groundedMethod.groundedNo);
								}
							}

							// create the correct name of the new method so that the plan extractor can extract the correct
							liftedMethod.name = "<" + liftedMethod.name + ";" + decomposedTaskName + ";" + unitLiftedMethod.name + ";";
							liftedMethod.name += std::to_string(positionOfExpanded) + ";";
							for (size_t i = 0; i < idmapping.size(); i++){
								if (i) liftedMethod.name += ",";
								liftedMethod.name += std::to_string(idmapping[i]);
							}
							liftedMethod.name += ">";
							
							if (unitGroundedMethod.groundedPreconditions.size() == 0) break;
						}
					}
	
					if (!found)
						break;
				}
				// write back the new method, i.e. add the lifted version to the domain
				// the grounded one is a reference, so it does not need to be written back
				groundedMethod.methodNo = domain.decompositionMethods.size();
				const_cast<Domain &>(domain).decompositionMethods.push_back(liftedMethod);
			}	
		}
	}
}

void removeEmptyMethodPreconditions(const Domain & domain,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		std::vector<GroundedTask> & inputTasksGroundedPg,
		std::vector<GroundedMethod> & inputMethodsGroundedTdg){

	std::vector<std::set<int>> taskToMethodsTheyAreContainedIn (inputTasksGroundedPg.size());
	for (auto & method : inputMethodsGroundedTdg){
		if (prunedMethods[method.groundedNo]) continue;
		for (size_t subTaskIdx = 0; subTaskIdx < method.groundedPreconditions.size(); subTaskIdx++)
			taskToMethodsTheyAreContainedIn[method.groundedPreconditions[subTaskIdx]].insert(method.groundedNo);
	}


	// find method precondition actions that have no unpruned preconditions
	std::vector<bool> prunableMethodPrecondition(inputMethodsGroundedTdg.size());
	for (GroundedTask & task : inputTasksGroundedPg){
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;
		//std::cout << "Is prim " << domain.tasks[task.taskNo].name << std::endl;
		if (domain.tasks[task.taskNo].name.rfind("__method_precondition_",0) != 0) continue;
		bool unprunedCondition = false;
		//std::cout << "checking " << domain.tasks[task.taskNo].name << " ... ";
		for (int & pre : task.groundedPreconditions) if (!prunedFacts[pre]) { unprunedCondition  = true; break; }
		for (int & add : task.groundedAddEffects)    if (!prunedFacts[add]) { unprunedCondition  = true; break; }
		for (int & del : task.groundedDelEffects)    if (!prunedFacts[del]) { unprunedCondition  = true; break; }
		//std::cout << unprunedPrecondition << std::endl;
		if (unprunedCondition) continue;

		// this task is now pruned
		prunedTasks[task.groundedNo] = true;

		// so remove it from all methods this task is contained in	
		for (const int & method : taskToMethodsTheyAreContainedIn[task.groundedNo]){
			if (prunedMethods[method]) continue;
			GroundedMethod & groundedMethod = inputMethodsGroundedTdg[method];
			// copy the lifted method
			DecompositionMethod liftedMethod = domain.decompositionMethods[groundedMethod.methodNo];
			DEBUG( std::cerr << "removing task " << task.groundedNo << " from method " << method << " " << liftedMethod.name << std::endl);
			
			for (size_t subTaskIdx = 0; subTaskIdx < liftedMethod.subtasks.size(); subTaskIdx++){
				if (groundedMethod.groundedPreconditions[subTaskIdx] != task.groundedNo) continue; 

				std::vector<std::pair<int,int>> orderPertainingToThisTask;
				std::vector<std::pair<int,int>> orderNotPertainingToThisTask;
				for(auto order : liftedMethod.orderingConstraints)
					if (order.first == subTaskIdx || order.second == subTaskIdx)
						orderPertainingToThisTask.push_back(order);
					else 
						orderNotPertainingToThisTask.push_back(order);

				// if the method we have to apply is empty
				groundedMethod.groundedPreconditions.erase(groundedMethod.groundedPreconditions.begin() + subTaskIdx);
				liftedMethod.subtasks.erase(liftedMethod.subtasks.begin() + subTaskIdx);
				for (auto a : orderPertainingToThisTask) {
					if (a.second != subTaskIdx) continue;
					for (auto b : orderPertainingToThisTask) {
						if (b.first != subTaskIdx) continue;
						orderNotPertainingToThisTask.push_back(std::make_pair(a.first,b.second));
					}
				}
				liftedMethod.orderingConstraints.clear();
				for (auto order : orderNotPertainingToThisTask){
					if (order.first > subTaskIdx) order.first--;
					if (order.second > subTaskIdx) order.second--;
					liftedMethod.orderingConstraints.push_back(order);
				}
			
			
				std::vector<int> newOrder;
				for (size_t i = 0; i < groundedMethod.preconditionOrdering.size(); i++){
					if (groundedMethod.preconditionOrdering[i] != subTaskIdx){
						bool afterDeleted = groundedMethod.preconditionOrdering[i] > subTaskIdx;
						newOrder.push_back(groundedMethod.preconditionOrdering[i] - (afterDeleted?1:0));
					}
				}
				groundedMethod.preconditionOrdering = newOrder;

				//subTaskIdx--;
			}

			// write back the new method, i.e. add the lifted version to the domain
			// the grounded one is a reference, so it does not need to be written back
			groundedMethod.methodNo = domain.decompositionMethods.size();
			const_cast<Domain &>(domain).decompositionMethods.push_back(liftedMethod);
		}
	}
}



void contract_consecutive_primitives(const Domain & domain, const Problem & problem,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		std::vector<GroundedTask> & inputTasksGroundedPg,
		std::vector<GroundedMethod> & inputMethodsGroundedTdg){

	std::vector<Task> newTasks;
	std::vector<GroundedTask> newGroundTasks;
	
	std::vector<DecompositionMethod> newMethods;
	std::vector<GroundedMethod> newGroundMethods;

	for (auto & method : inputMethodsGroundedTdg){
		if (prunedMethods[method.groundedNo]) continue;
		if (method.groundedPreconditions.size() < 2) continue; // can't compact anything

		DEBUG(std::cout << "Method: " << method.groundedPreconditions.size() << std::endl);
		
		std::vector<std::vector<int>> segmentation;
		std::vector<int> currentPrimitiveBlock;
		for (size_t currentSubtask = 0; currentSubtask < method.groundedPreconditions.size(); currentSubtask++){
			int actualSubtaskIndex = method.preconditionOrdering[currentSubtask];
			// ground ID of the subtask
			int groundedSubtask = method.groundedPreconditions[actualSubtaskIndex];

			GroundedTask & groundTask = inputTasksGroundedPg[groundedSubtask];
			int liftedTaskNumber = groundTask.taskNo;

			DEBUG(std::cout << "\tmethod subtask #" << currentSubtask << " gID=" << groundedSubtask << " lID=" << liftedTaskNumber << " nPim=" << domain.nPrimitiveTasks << std::endl);

			if (liftedTaskNumber < domain.nPrimitiveTasks){
				DEBUG(std::cout << "\t\tis primitive" << std::endl);
				currentPrimitiveBlock.push_back(groundedSubtask);
			} else {
				DEBUG(std::cout << "\t\tis abstract" << std::endl);
				if (currentPrimitiveBlock.size())
					segmentation.push_back(currentPrimitiveBlock);
				currentPrimitiveBlock.clear();
				
				// add a singular block with the abstract task
				currentPrimitiveBlock.push_back(groundedSubtask);
				segmentation.push_back(currentPrimitiveBlock);
				currentPrimitiveBlock.clear();
			}
		}
		// if the method ends with a primitive block, add it to the segmentation
		if (currentPrimitiveBlock.size())
			segmentation.push_back(currentPrimitiveBlock);

		bool largerThanOne = false;
		for (auto & x : segmentation) largerThanOne |= x.size() > 1;

		if (!largerThanOne) continue;
		
		DEBUG(std::cout << "\tmethod has (at least one) block of primitives" << std::endl);



		std::vector<int> methodTasks;
		bool methodNotExecutable = false;
		for (auto & segment : segmentation) {
			assert(segment.size());
			if (segment.size() == 1){
				methodTasks.push_back(segment[0]);
				continue;
			}

			DEBUG(std::cout << "\tCompactifying action block" << std::endl);
			
			std::unordered_set<int> pre;
			std::unordered_set<int> add;
			std::unordered_set<int> del;

			for (int groundAction : segment){
				DEBUG(std::cout << "\t\taction" << std::endl);
				GroundedTask & groundTask = inputTasksGroundedPg[groundAction];
				
				for (int myPre : groundTask.groundedPreconditions){
					DEBUG(std::cout << "\t\t\tpre " << myPre << std::endl);
					if (del.count(myPre)) methodNotExecutable = true;
					if (add.count(myPre)) continue; // precondition automatically satisfied
					pre.insert(myPre);
				}

				// first del then add to keep the precedence between them
				for (int myDel : groundTask.groundedDelEffects){
					DEBUG(std::cout << "\t\t\tdel " << myDel << std::endl);
					del.insert(myDel);
					add.erase(myDel); // if feature was previously deleted, it is not any more
				}
				
				for (int myAdd : groundTask.groundedAddEffects){
					DEBUG(std::cout << "\t\t\tadd " << myAdd << std::endl);
					add.insert(myAdd);
					del.erase(myAdd); // if feature was previously deleted, it is not any more
				}
			}
			if (methodNotExecutable) break;
		
			DEBUG(std::cout << "\tinferred new action" << std::endl);
		
			DEBUG(for (int myPre : pre) std::cout << "\t\t\tpre " << myPre << std::endl);
			DEBUG(for (int myAdd : add) std::cout << "\t\t\tadd " << myAdd << std::endl);
			DEBUG(for (int myDel : del) std::cout << "\t\t\tdel " << myDel << std::endl);
		

			// create new primitive action (grounded version)
			GroundedTask newGroundAction;
			newGroundAction.groundedNo = inputTasksGroundedPg.size() + newTasks.size();
			newGroundAction.taskNo = domain.nPrimitiveTasks + newTasks.size(); // have it temporarily negative for detecting these cases when adding the tasks to the domain proper
			for (int myPre : pre) newGroundAction.groundedPreconditions.push_back(myPre);
			for (int myAdd : add) newGroundAction.groundedAddEffects.push_back(myAdd);
			for (int myDel : del) newGroundAction.groundedDelEffects.push_back(myDel);
			// push back all variables of all sub actions
			for (int groundAction : segment){
				GroundedTask & groundTask = inputTasksGroundedPg[groundAction];
				for (int & c : groundTask.arguments)
					newGroundAction.arguments.push_back(c);
			}
			
			// record number of new action
			methodTasks.push_back(-inputTasksGroundedPg.size() - newGroundTasks.size());
			// add action to list of actions to add
			newGroundTasks.push_back(newGroundAction);

			// create new primitive action (lifted version)
			Task newLiftedAction;
			newLiftedAction.name = "%aggregate";
			for (int groundAction : segment){
				GroundedTask & groundTask = inputTasksGroundedPg[groundAction];
				newLiftedAction.name += "#" + domain.tasks[groundTask.taskNo].name + "#" + std::to_string(groundTask.arguments.size());
			}
			newLiftedAction.name += "$";
			DEBUG(std::cout << "\tCreating new lifted action: " << newLiftedAction.name << std::endl);
		   
			newLiftedAction.number_of_original_variables = newGroundAction.arguments.size();
			newLiftedAction.isCompiledConditionalEffect = false;
			newTasks.push_back(newLiftedAction);
		}

		// if the method contains a non executable sequence of actions, just prune it!
		if (methodNotExecutable){
			prunedMethods[method.groundedNo] = true;
			DEBUG(std::cout << "\tMethod is not executable ... " << std::endl);
			continue;
		}
		
		// remove the previous version of the method
		prunedMethods[method.groundedNo] = true;
		DecompositionMethod mainLiftedMethod = domain.decompositionMethods[method.methodNo];

		// create a new method for this
		DecompositionMethod liftedMethod;
		liftedMethod.name = mainLiftedMethod.name;
		liftedMethod.taskNo = mainLiftedMethod.taskNo;
		liftedMethod.variableSorts = mainLiftedMethod.variableSorts;
		liftedMethod.taskParameters = mainLiftedMethod.taskParameters;

		// create sequence of subtasks	
		int current = 0;	
		for (int & groundedSubTask : methodTasks){
			TaskWithArguments nextSubtask;
			if (groundedSubTask >= 0){
				nextSubtask.taskNo = inputTasksGroundedPg[groundedSubTask].taskNo;
			} else {
				int no = groundedSubTask + inputTasksGroundedPg.size();
				no *= -1;
				nextSubtask.taskNo = newGroundTasks[no].taskNo;
				groundedSubTask *= -1;
			}
			liftedMethod.subtasks.push_back(nextSubtask);
			if (current) liftedMethod.orderingConstraints.push_back(std::make_pair(current-1,current));
			current++;
		}
		
		// add lifted version of the method to domain
		int liftedMethodNumber = domain.decompositionMethods.size() + newMethods.size();
		newMethods.push_back(liftedMethod);

		// add the grounded method
		GroundedMethod newMethod;
		newMethod.methodNo = liftedMethodNumber;
		newMethod.arguments = method.arguments;
		newMethod.groundedAddEffects = method.groundedAddEffects;
		newMethod.groundedPreconditions = methodTasks; // reduced tasks are the subtasks of this method
		for (int i = 0; i < methodTasks.size(); i++)
			newMethod.preconditionOrdering.push_back(i);
		newMethod.groundedNo = inputMethodsGroundedTdg.size() + newGroundMethods.size();

		// add the grounded method
		newGroundMethods.push_back(newMethod);
	}


	// renumber the (lifted) abstract tasks as we have introduced new primitive ones ...
	for (int i = 0 ; i < inputTasksGroundedPg.size(); i++){
		if (inputTasksGroundedPg[i].taskNo >= domain.nPrimitiveTasks){
			// it is abstract has has to be re-numbered
			inputTasksGroundedPg[i].taskNo += newTasks.size();
		}
	}
	// add the new ones
	for (GroundedTask & newGroundTask : newGroundTasks){
		inputTasksGroundedPg.push_back(newGroundTask);
		prunedTasks.push_back(false);
	}

	// lifted tasks ...
	std::vector<Task> oldTasks = const_cast<Domain &>(domain).tasks;
	const_cast<Domain &>(domain).tasks.clear(); // remove the old
	for (int i = 0; i < domain.nPrimitiveTasks; i++)
		const_cast<Domain &>(domain).tasks.push_back(oldTasks[i]);

	// insert the new primitives right in the middle
	for (int i = 0; i < newTasks.size(); i++)
		const_cast<Domain &>(domain).tasks.push_back(newTasks[i]);
	
	for (int i = domain.nPrimitiveTasks; i < domain.nTotalTasks; i++)
		const_cast<Domain &>(domain).tasks.push_back(oldTasks[i]);

	////// tasks are now fixed. Methods can just be added at the end

	// add the methods
	for (DecompositionMethod & m : newMethods){
		// add lifted methods
		const_cast<Domain &>(domain).decompositionMethods.push_back(m);
	}

	// fix numbers in methods
	for (DecompositionMethod & m : const_cast<Domain &>(domain).decompositionMethods){
		m.taskNo += newTasks.size(); // the decomposed task is always abstract ...
		
		for (TaskWithArguments & t : m.subtasks){
			if (t.taskNo < 0){
				t.taskNo *= -1;
			} else if (t.taskNo >= domain.nPrimitiveTasks)
				t.taskNo += newTasks.size();
		}
	}

	for (GroundedMethod & m : newGroundMethods){
		// add as method to the task it decomposes
		inputTasksGroundedPg[*(m.groundedAddEffects.begin())].groundedDecompositionMethods.push_back(inputMethodsGroundedTdg.size());
		// add the grounded method
		inputMethodsGroundedTdg.push_back(m);
		prunedMethods.push_back(false);
	}
	
	//// fix the numbers of the grounded methods ...
	//for (GroundedMethod & m : inputMethodsGroundedTdg){
	//	for (int & add : m.groundedAddEffects){
	//		if (add < 0){
	//			add *= -1;
	//		} else if (add >= domain.nPrimitiveTasks)
	//			add += newTasks.size();
	//	}
	//	
	//	for (int & pre : m.groundedPreconditions){
	//		if (pre < 0){
	//			pre *= -1;
	//		} else if (pre >= domain.nPrimitiveTasks)
	//			pre += newTasks.size();
	//	}
	//}

	const_cast<Domain &>(domain).nPrimitiveTasks += newTasks.size();
	const_cast<Domain &>(domain).nTotalTasks += newTasks.size();
	const_cast<Problem &>(problem).initialAbstractTask += newTasks.size();
}


void change_to_methods_with_at_most_two_tasks(const Domain & domain,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		std::vector<GroundedTask> & inputTasksGroundedPg,
		std::vector<GroundedMethod> & inputMethodsGroundedTdg){
	
	std::vector<Task> newTasks;
	std::vector<DecompositionMethod> newMethods;
	std::vector<GroundedTask> newGroundTasks;
	std::vector<GroundedMethod> newGroundMethods;

	for (auto & method : inputMethodsGroundedTdg){
		if (prunedMethods[method.groundedNo]) continue;

		// if the method has at most two subtasks, it is ok
		if (method.groundedPreconditions.size() <= 2) continue;

		DEBUG(std::cout << "Method too large: " << method.groundedPreconditions.size() << std::endl);
		prunedMethods[method.groundedNo] = true;
		DecompositionMethod mainLiftedMethod = domain.decompositionMethods[method.methodNo];

		// we can only do this compilation (currently) for totally-ordered methods ...
		// TODO: do this in general for SHOP decompositions
		
		// use the precondition ordering for cutting the method into pieces
		int currentAT = method.groundedAddEffects[0];
		for (size_t currentSubtask = 0; currentSubtask < method.groundedPreconditions.size() - 2; currentSubtask++){
			DEBUG(std::cout << "  Creating method containing " << currentSubtask << std::endl);
			// create next task
			Task newIntermediateTask;
			newIntermediateTask.name = "_!_intermediate_task_method_" + std::to_string(method.groundedNo) + "_" + std::to_string(currentSubtask);
			newIntermediateTask.number_of_original_variables = 0;
			newIntermediateTask.isCompiledConditionalEffect = false;
			// decomposition methods in the lifted model don't need to be filled
			const_cast<Domain &>(domain).tasks.push_back(newIntermediateTask);
			const_cast<Domain &>(domain).nAbstractTasks++;
			const_cast<Domain &>(domain).nTotalTasks++;
			
			// create the ground instance
			GroundedTask groundedIntermediateTask;
			groundedIntermediateTask.groundedNo = prunedTasks.size();
			groundedIntermediateTask.taskNo = domain.tasks.size() - 1;
			inputTasksGroundedPg.push_back(groundedIntermediateTask);
			prunedTasks.push_back(false); // add the task

			// create a method decomposing the current AT into the current Subtask and the next AT
		
		
			// create a new method
			DecompositionMethod liftedMethod;
			liftedMethod.name = mainLiftedMethod.name;
			// only add the _i if we are not the first method (for plan reconstruction)
		   	if (currentSubtask)	liftedMethod.name += "_" + std::to_string(currentSubtask);
			liftedMethod.taskNo = inputTasksGroundedPg[currentAT].taskNo;
			liftedMethod.variableSorts = mainLiftedMethod.variableSorts;
			// if this is the initial one, it will have task parameters
			if (currentSubtask == 0)
				liftedMethod.taskParameters = mainLiftedMethod.taskParameters;
			// else keep them empty
			
			int actualSubtaskIndex = method.preconditionOrdering[currentSubtask];
			liftedMethod.subtasks.push_back(mainLiftedMethod.subtasks[actualSubtaskIndex]);
			TaskWithArguments nextSubtask;
			nextSubtask.taskNo = groundedIntermediateTask.taskNo;
			liftedMethod.subtasks.push_back(nextSubtask);
			liftedMethod.orderingConstraints.push_back(std::make_pair(0,1));
			int liftedMethodNumber = domain.decompositionMethods.size() + newMethods.size();
			newMethods.push_back(liftedMethod);

			// add the grounded method
			GroundedMethod newMethod;
			newMethod.methodNo = liftedMethodNumber;
			newMethod.arguments = method.arguments;
			newMethod.groundedAddEffects.push_back(currentAT);
			newMethod.groundedPreconditions.push_back(method.groundedPreconditions[actualSubtaskIndex]);
			newMethod.groundedPreconditions.push_back(groundedIntermediateTask.groundedNo);
			newMethod.preconditionOrdering.push_back(0);
			newMethod.preconditionOrdering.push_back(1);
			newMethod.groundedNo = inputMethodsGroundedTdg.size() + newGroundMethods.size();
			

			// add the grounded method
			newGroundMethods.push_back(newMethod);
				
			currentAT = groundedIntermediateTask.groundedNo;
		}

		// create last method
		DecompositionMethod liftedMethod;
		liftedMethod.name = mainLiftedMethod.name;
		liftedMethod.name += "_" + std::to_string(method.groundedPreconditions.size() - 2);
		liftedMethod.taskNo = inputTasksGroundedPg[currentAT].taskNo;
		liftedMethod.variableSorts = mainLiftedMethod.variableSorts;
		
		int actualSubtaskIndex1 = method.preconditionOrdering[method.groundedPreconditions.size() - 2];
		int actualSubtaskIndex2 = method.preconditionOrdering[method.groundedPreconditions.size() - 1];

		liftedMethod.subtasks.push_back(mainLiftedMethod.subtasks[actualSubtaskIndex1]);
		liftedMethod.subtasks.push_back(mainLiftedMethod.subtasks[actualSubtaskIndex2]);
		liftedMethod.orderingConstraints.push_back(std::make_pair(0,1));
		int liftedMethodNumber = domain.decompositionMethods.size() + newMethods.size();
		newMethods.push_back(liftedMethod);

		// add the grounded method
		GroundedMethod newMethod;
		newMethod.methodNo = liftedMethodNumber;
		newMethod.arguments = method.arguments;
		newMethod.groundedAddEffects.push_back(currentAT);
		newMethod.groundedPreconditions.push_back(method.groundedPreconditions[actualSubtaskIndex1]);
		newMethod.groundedPreconditions.push_back(method.groundedPreconditions[actualSubtaskIndex2]);
		newMethod.preconditionOrdering.push_back(0);
		newMethod.preconditionOrdering.push_back(1);
		newMethod.groundedNo = inputMethodsGroundedTdg.size() + newGroundMethods.size();
		

		// add the grounded method
		newGroundMethods.push_back(newMethod);
	}
	
	for (DecompositionMethod & m : newMethods){
		const_cast<Domain &>(domain).decompositionMethods.push_back(m);
	}
	
	for (GroundedMethod & m : newGroundMethods){
		// add as method to the task it decomposes
		inputTasksGroundedPg[*(m.groundedAddEffects.begin())].groundedDecompositionMethods.push_back(inputMethodsGroundedTdg.size());
		
		inputMethodsGroundedTdg.push_back(m);
		prunedMethods.push_back(false);
	}
	
	//exit(1);
}



void postprocess_grounding(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		bool & reachabilityNecessary,
		grounding_configuration & config){
	// sort the subtasks of each method topologically s.t. 
	sortSubtasksOfMethodsTopologically(domain, prunedTasks, prunedMethods, reachableMethods);
		
	
	if (!config.quietMode) std::cerr << "Simplifying instance." << std::endl;
	if (config.removeUselessPredicates) {
		if (!config.quietMode) std::cerr << "Removing useless facts/literals" << std::endl;
		removeUnnecessaryFacts(domain, problem, prunedTasks, prunedFacts, reachableTasks, reachableFacts);
	}

	if (config.pruneEmptyMethodPreconditions){
		if (!config.quietMode) std::cerr << "Removing method precondition actions whose precondition is empty" << std::endl;
		removeEmptyMethodPreconditions(domain,prunedFacts,prunedTasks,prunedMethods,reachableTasks,reachableMethods);
	}

	// this MUST be the (second) last step. Else the information stored inside the method names for reconstruction becomes invalid
	if (config.expandChoicelessAbstractTasks){
		if (!config.quietMode) std::cerr << "Expanding abstract tasks with only one method" << std::endl;
		expandAbstractTasksWithSingleMethod(domain, problem, prunedTasks, prunedMethods, reachableTasks, reachableMethods, config.keepTwoRegularisation);
	}

	if (config.compactConsecutivePrimitives){
		if (!config.quietMode) std::cerr << "Compacting consecutive primitives in methods" << std::endl;
		contract_consecutive_primitives(domain, problem, prunedTasks, prunedMethods, reachableTasks, reachableMethods);
		reachabilityNecessary = true;
	}

	if (config.atMostTwoTasksPerMethod){
		if (!config.quietMode) std::cerr << "Changing all methods s.t. they contain at most two tasks." << std::endl;
		change_to_methods_with_at_most_two_tasks(domain, prunedTasks, prunedMethods, reachableTasks, reachableMethods);
	}
}
