#include "conditional_effects.h"
#include "debug.h"
#include <iostream>

PredicateWithArguments convertToNewVariables(std::map<int,int> & variablesOfMainToCE, PredicateWithArguments old){
	PredicateWithArguments n;
	n.predicateNo = old.predicateNo;
	for (int arg : old.arguments){
		auto it = variablesOfMainToCE.find(arg);
		if (it != variablesOfMainToCE.end())
			n.arguments.push_back(it->second);
		else {
			int nVar = variablesOfMainToCE.size();
			variablesOfMainToCE[arg] = nVar;
			n.arguments.push_back(nVar);
		}
	}

	return n;
}


void expand_conditional_effects_into_artificial_tasks(Domain & domain, Problem & problem){
	// we add new tasks to the model representing the conditional effects. For this to work, we have to renumber the abstract tasks (else the GPG implementation breaks).
	// this change as to be propagated into methods, their task networks and to the initial abstract task	
	
	std::vector<Task> newTasks;
	// primitive actions retain their number
	newTasks.insert(newTasks.end(), domain.tasks.begin(), domain.tasks.begin() + domain.nPrimitiveTasks);

	int number_of_added_tasks = 0;
	// go through all primitive tasks and check for conditional effects
	for (size_t taskNo = 0; taskNo < domain.nPrimitiveTasks; taskNo++){
		Task & task = domain.tasks[taskNo];
		if (task.conditionalAdd.size() + task.conditionalDel.size() == 0) continue;
		
		// add a task for every CE, bool=true indicates add, else del
		std::vector<std::pair<bool,std::pair<std::vector<PredicateWithArguments>, PredicateWithArguments>>> all_ces;
		
		for (auto & add : task.conditionalAdd)
			all_ces.push_back(std::make_pair(true,add));
		for (auto & del : task.conditionalDel)
			all_ces.push_back(std::make_pair(false,del));

		int instance = 0;
		for (auto & ce : all_ces){
			std::map<int,int> variablesOfMainToCE;

			Task ceTask;
			ceTask.type = Task::PRIMITIVE;
			ceTask.isCompiledConditionalEffect = true;
			ceTask.name = task.name + "_ce_" + std::to_string(instance++);
			ceTask.number_of_original_variables = 0; // does not matter
			for (PredicateWithArguments pre : ce.second.first)
				ceTask.preconditions.push_back(convertToNewVariables(variablesOfMainToCE,pre));
					
			if (ce.first)
				ceTask.effectsAdd.push_back(convertToNewVariables(variablesOfMainToCE,ce.second.second));
			else
				ceTask.effectsDel.push_back(convertToNewVariables(variablesOfMainToCE,ce.second.second));

	
			// build the guard predicate
			std::vector<int> ceVarsToMain (variablesOfMainToCE.size());
			for (auto v : variablesOfMainToCE)
				ceVarsToMain[v.second] = v.first;
			Predicate guard;
			guard.name = ceTask.name + "_guard#";
			guard.guard_for_conditional_effect = true;
			for (size_t i = 0; i < ceVarsToMain.size(); i++){
				DEBUG(std::cout << task.name << " " << i << " " << ceVarsToMain[i] << " " << task.variableSorts.size() << " " << std::endl);
				guard.argumentSorts.push_back(task.variableSorts[ceVarsToMain[i]]);
			}

			// get id of the guard and add it to the predicates
			int guard_predicate_number = domain.predicates.size();
			domain.predicates.push_back(guard);
			
			// build variable list of ceTask
			for (size_t i = 0; i < ceVarsToMain.size(); i++)
				ceTask.variableSorts.push_back(task.variableSorts[ceVarsToMain[i]]);

			// for CE task
			PredicateWithArguments guardLiteral;
			guardLiteral.predicateNo = guard_predicate_number;
			for (size_t i = 0; i < ceVarsToMain.size(); i++)
				guardLiteral.arguments.push_back(i);

			// add the guard as an additional precondition
			ceTask.preconditions.push_back(guardLiteral);

			// for main task
			guardLiteral.arguments.clear();
			for (size_t i = 0; i < ceVarsToMain.size(); i++)
				guardLiteral.arguments.push_back(ceVarsToMain[i]);

			// add the guard as an add effect to the main task
			newTasks[taskNo].effectsAdd.push_back(guardLiteral);

			
			number_of_added_tasks++;
			newTasks.push_back(ceTask);
		}
	}
	
	// correct numbers of abstract tasks
	for (DecompositionMethod & m : domain.decompositionMethods){
		m.taskNo += number_of_added_tasks; // is abstract so it will be pushed back

		for (TaskWithArguments & t : m.subtasks){
			if (t.taskNo < domain.nPrimitiveTasks) continue; // is primitive, will not be moved
			t.taskNo += number_of_added_tasks;
		}
	}

	// finally add abstract tasks
	newTasks.insert(newTasks.end(), domain.tasks.begin() + domain.nPrimitiveTasks, domain.tasks.end());
	
	// adjust numbers
	problem.initialAbstractTask += number_of_added_tasks;
	domain.nPrimitiveTasks += number_of_added_tasks;
	domain.nTotalTasks += number_of_added_tasks;


	// write back the tasks
	domain.tasks = newTasks;
}

