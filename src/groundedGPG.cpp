#include <iostream>
#include <cassert>
#include <unistd.h>
#include <vector>
#include <tuple>
#include <queue>

#include "groundedGPG.h"
#include "debug.h"
#include "model.h"


std::pair<size_t, size_t> groundedPg (std::vector<bool> & factReached, std::vector<int> & unfulfilledPreconditions, std::vector<bool> & prunedTasks, std::vector<bool> & prunedFacts, const std::vector<GroundedTask> & inputTasks, const std::vector<Fact> & inputFacts, const Domain & domain, const Problem & problem)
{
	// Reset output vectors
	factReached.clear ();
	factReached.resize (inputFacts.size ());
	unfulfilledPreconditions.clear ();
	unfulfilledPreconditions.resize (inputTasks.size ());

	// Number of reached tasks/facts - allows for fast checks whether some tasks/facts were pruned
	size_t reachedTasksCount = 0;
	size_t reachedFactsCount = 0;

	std::queue<int> factsToBeProcessed;

	// Initialize number of unfulfilled preconditions for each task
	for (size_t taskIdx = 0; taskIdx < inputTasks.size (); ++taskIdx)
	{
		const GroundedTask & task = inputTasks[taskIdx];
		if (task.taskNo >= domain.nPrimitiveTasks)
			continue;

		if (prunedTasks[taskIdx])
			continue;

		unfulfilledPreconditions[taskIdx] = task.groundedPreconditions.size ();
		if (unfulfilledPreconditions[taskIdx] == 0)
		{
			++reachedTasksCount;

			for (int addFact : task.groundedAddEffects)
			{
				if (!factReached[addFact])
				{
					factsToBeProcessed.push (addFact);
					factReached[addFact] = true;
					++reachedFactsCount;
					DEBUG(std::cerr << "Reached fact " << addFact << " for the first time (task without preconditions)." << std::endl);
				}
			}
		}
	}

	DEBUG(std::cerr << "Before Grounded PG:" << std::endl;
	for (size_t taskIdx = 0; taskIdx < inputTasks.size (); ++taskIdx)
	{
		const GroundedTask & task = inputTasks[taskIdx];
		if (task.taskNo < domain.nPrimitiveTasks)
			std::cerr << "    Task " << taskIdx << " (" << task.groundedNo << ", primitive): " << unfulfilledPreconditions[task.groundedNo] << " vs " << domain.tasks[task.taskNo].preconditions.size () << " (unfulfilled vs preconditions), "
				<< task.groundedDecompositionMethods.size () << " grounded decomposition methods (vs " << domain.tasks[task.taskNo].decompositionMethods.size () << ")." << std::endl;
		else
			std::cerr << "    Task " << taskIdx << " (" << task.groundedNo << ",  abstract): " << unfulfilledPreconditions[task.groundedNo] << " vs " << domain.tasks[task.taskNo].preconditions.size () << " (unfulfilled vs preconditions), "
				<< task.groundedDecompositionMethods.size () << " grounded decomposition methods (vs " << domain.tasks[task.taskNo].decompositionMethods.size () << ")." << std::endl;
	});

	// Calculate which tasks have a specific fact as a precondition
	std::vector<std::vector<int>> tasksByPrecondition (inputFacts.size ());
	for (size_t taskIdx = 0; taskIdx < inputTasks.size (); ++taskIdx)
	{
		const GroundedTask & task = inputTasks[taskIdx];
		if (task.taskNo >= domain.nPrimitiveTasks)
			continue;

		if (prunedTasks[taskIdx])
			continue;

		assert (task.groundedNo == taskIdx);

		for (int preconditionIdx : task.groundedPreconditions)
			tasksByPrecondition[preconditionIdx].push_back (taskIdx);
	}

	for (size_t initFactIdx = 0; initFactIdx < problem.init.size (); ++initFactIdx)
	{
		// Perhaps the init fact was already added by a task without preconditions?
		if (factReached[initFactIdx])
			continue;

		// XXX: assumes that the first facts in the list are the init facts
		factsToBeProcessed.push (initFactIdx);

		factReached[initFactIdx] = true;
		++reachedFactsCount;
	}

	while (!factsToBeProcessed.empty ())
	{
		int factIdx = factsToBeProcessed.front ();
		factsToBeProcessed.pop ();

		for (int taskIdx : tasksByPrecondition[factIdx])
		{
			const GroundedTask & task = inputTasks[taskIdx];

			--unfulfilledPreconditions[taskIdx];
			if (unfulfilledPreconditions[taskIdx] == 0)
			{
				++reachedTasksCount;
				for (int addFact : task.groundedAddEffects)
				{
					if (!factReached[addFact])
					{
						factsToBeProcessed.push (addFact);
						factReached[addFact] = true;
						++reachedFactsCount;
					}
				}
			}
		}
	}

	// Prune tasks and facts
	for (size_t taskIdx = 0; taskIdx < inputTasks.size (); ++taskIdx)
		if (unfulfilledPreconditions[taskIdx] > 0)
			prunedTasks[taskIdx] = true;
	for (size_t factIdx = 0; factIdx < inputFacts.size (); ++factIdx)
		if (!factReached[factIdx])
			prunedFacts[factIdx] = true;

	return {reachedTasksCount, reachedFactsCount};
}

std::pair<size_t, size_t> groundedTdg (std::vector<bool> & taskReached, std::vector<int> & unfulfilledPreconditions, std::vector<bool> & prunedMethods, std::vector<bool> & prunedTasks, const std::vector<GroundedMethod> & inputMethods, const std::vector<GroundedTask> & inputTasks, const Domain & domain, const Problem & problem)
{
	// Reset output vectors
	taskReached.clear ();
	taskReached.resize (inputTasks.size ());
	unfulfilledPreconditions.clear ();
	unfulfilledPreconditions.resize (inputMethods.size ());

	// Number of reached methods/tasks - allows for fast checks whether some methods/tasks were pruned
	size_t reachedMethodsCount = 0;
	size_t reachedTasksCount = 0;

	std::queue<int> tasksToBeProcessed;

	// Initialize number of unfulfilled preconditions for each method
	for (size_t methodIdx = 0; methodIdx < inputMethods.size (); ++methodIdx)
	{
		if (prunedMethods[methodIdx])
			continue;

		const GroundedMethod & method = inputMethods[methodIdx];
		unfulfilledPreconditions[methodIdx] = method.groundedPreconditions.size ();
		if (unfulfilledPreconditions[methodIdx] == 0)
		{
			++reachedMethodsCount;

			for (int addTask : method.groundedAddEffects)
			{
				if (!taskReached[addTask])
				{
					tasksToBeProcessed.push (addTask);
					taskReached[addTask] = true;
					++reachedTasksCount;
				}
			}
		}
	}

	DEBUG(std::cerr << "Before Grounded TDG:" << std::endl;
	for (size_t methodIdx = 0; methodIdx < inputMethods.size (); ++methodIdx)
	{
		const GroundedMethod & method = inputMethods[methodIdx];
		std::cerr << "    Method " << methodIdx << " (" << method.groundedNo << "): " << unfulfilledPreconditions[method.groundedNo] << " vs " << domain.decompositionMethods[method.methodNo].subtasks.size () << " (unfulfilled vs subtasks), "
			<< method.groundedPreconditions.size () << " grounded preconditions (vs " << domain.decompositionMethods[method.methodNo].subtasks.size () << ")." << std::endl;
		for (int subtaskNo : method.groundedPreconditions)
			std::cerr << "        Subtask " << subtaskNo << std::endl;
	});

	// Calculate which methods have a specific task as a precondition
	std::vector<std::vector<int>> methodsByPrecondition (inputTasks.size ());
	for (size_t methodIdx = 0; methodIdx < inputMethods.size (); ++methodIdx)
	{
		if (prunedMethods[methodIdx])
			continue;

		const GroundedMethod & method = inputMethods[methodIdx];
		assert (method.groundedNo == methodIdx);

		for (int preconditionIdx : method.groundedPreconditions)
			methodsByPrecondition[preconditionIdx].push_back (methodIdx);
	}

	for (size_t initTaskIdx = 0; initTaskIdx < inputTasks.size (); ++initTaskIdx)
	{
		const GroundedTask & task = inputTasks[initTaskIdx];
		if (!prunedTasks[initTaskIdx] && task.taskNo < domain.nPrimitiveTasks)
		{
			taskReached[initTaskIdx] = true;
			tasksToBeProcessed.push (initTaskIdx);
		}
	}

	while (!tasksToBeProcessed.empty ())
	{
		int taskIdx = tasksToBeProcessed.front ();
		tasksToBeProcessed.pop ();

		for (int methodIdx : methodsByPrecondition[taskIdx])
		{
			const GroundedMethod & method = inputMethods[methodIdx];

			--unfulfilledPreconditions[methodIdx];
			if (unfulfilledPreconditions[methodIdx] == 0)
			{
				++reachedMethodsCount;
				for (int addFact : method.groundedAddEffects)
				{
					if (!taskReached[addFact])
					{
						tasksToBeProcessed.push (addFact);
						taskReached[addFact] = true;
						++reachedTasksCount;
					}
				}
			}
		}
	}

	// Prune methods and tasks
	size_t reachedPrimitiveTasksCount = 0;
	for (size_t methodIdx = 0; methodIdx < inputMethods.size (); ++methodIdx)
		if (unfulfilledPreconditions[methodIdx] > 0)
			prunedMethods[methodIdx] = true;
	for (size_t taskIdx = 0; taskIdx < inputTasks.size (); ++taskIdx)
	{
		if (taskReached[taskIdx])
		{
			if (inputTasks[taskIdx].taskNo < domain.nPrimitiveTasks)
				++reachedPrimitiveTasksCount;
		}
		else
		{
				prunedTasks[taskIdx] = true;
		}
	}

	return {reachedMethodsCount, reachedPrimitiveTasksCount};
}

// Returns the new number of the visited grounded task
void groundedInnerTdgDfs (std::vector<bool> & prunedTasks, std::vector<bool> & prunedMethods, const std::vector<GroundedTask> & inputTasks, const std::vector<GroundedMethod> & inputMethods, const Domain & domain, std::vector<bool> & visitedTasks, std::vector<bool> & visitedMethods, size_t groundedTaskIdx)
{
	if (visitedTasks[groundedTaskIdx])
		return;
	visitedTasks[groundedTaskIdx] = true;

	assert (!prunedTasks[groundedTaskIdx]);

	const GroundedTask & groundedTask = inputTasks[groundedTaskIdx];
	for (auto groundedMethodIdx : groundedTask.groundedDecompositionMethods)
	{
		if (prunedMethods[groundedMethodIdx])
			continue;
		visitedMethods[groundedMethodIdx] = true;

		const GroundedMethod & groundedMethod = inputMethods[groundedMethodIdx];
		for (int subtaskNo : groundedMethod.groundedPreconditions)
			groundedInnerTdgDfs (prunedTasks, prunedMethods, inputTasks, inputMethods, domain, visitedTasks, visitedMethods, subtaskNo);
	}
}

std::pair<size_t, size_t> groundedTdgDfs (std::vector<bool> & prunedTasks, std::vector<bool> & prunedMethods, const std::vector<GroundedTask> & inputTasks, const std::vector<GroundedMethod> & inputMethods, const Domain & domain, const Problem & problem)
{
	std::vector<bool> visitedTasks (inputTasks.size ());
	std::vector<bool> visitedMethods (inputMethods.size ());

	for (const GroundedTask & task : inputTasks)
	{
		if (task.taskNo != problem.initialAbstractTask)
			continue;
		if (!prunedTasks[task.groundedNo])
			groundedInnerTdgDfs (prunedTasks, prunedMethods, inputTasks, inputMethods, domain, visitedTasks, visitedMethods, task.groundedNo);
		else {
			//std::cout << 
		}
	}

	size_t reachedPrimitiveTasksCount = 0;
	size_t reachedMethodsCount = 0;

	// Prune tasks and methods
	for (size_t taskIdx = 0; taskIdx < inputTasks.size (); ++taskIdx)
	{
		if (visitedTasks[taskIdx])
		{
			if (inputTasks[taskIdx].taskNo < domain.nPrimitiveTasks)
				++reachedPrimitiveTasksCount;
		}
		else
		{
			// check if this is a condition effect action
			if (!prunedTasks[taskIdx] && domain.tasks[inputTasks[taskIdx].taskNo].isCompiledConditionalEffect)
			{
				reachedPrimitiveTasksCount++;
			}
			else
			{
				prunedTasks[taskIdx] = true;
			}
		}
	}
	for (size_t methodIdx = 0; methodIdx < inputMethods.size (); ++methodIdx)
	{
		if (visitedMethods[methodIdx])
			++reachedMethodsCount;
		else
			prunedMethods[methodIdx] = true;
	}

	return {reachedPrimitiveTasksCount, reachedMethodsCount};
}


void run_grounded_HTN_GPG(const Domain & domain, const Problem & problem,  
		std::vector<Fact> reachableFacts,
		std::vector<GroundedTask> reachableTasks,
		std::vector<GroundedMethod> reachableMethods,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		grounding_configuration & config,
		bool alwaysRunDFS)
{
	// don't to anything for grounded problems
	if (problem.initialAbstractTask == -1)
		return;

	size_t remainingFactsCount = reachableTasks.size ();
	size_t remainingMethodsCount = reachableMethods.size ();

	size_t remainingPrimitiveTasks = 0;
	for (const auto & task : reachableTasks)
	{
		if (task.taskNo < domain.nPrimitiveTasks)
			++remainingPrimitiveTasks;
	}

	// Iterate grounded PG and TDG until convergence
	while (true)
	{
		// Grounded PG
		std::vector<bool> factReached;
		std::vector<int> unfulfilledPreconditions;
		auto [reachedTasksCount, reachedFactsCount] = groundedPg (factReached, unfulfilledPreconditions, prunedTasks, prunedFacts, reachableTasks, reachableFacts, domain, problem);

		if (!config.quietMode) std::cerr << "Grounded PG:" << std::endl;
		if (!config.quietMode) std::cerr << "Input was [" << remainingPrimitiveTasks << ", " << remainingFactsCount << "], output was [" << reachedTasksCount << ", " << reachedFactsCount << "]." << std::endl;
#ifdef PRINT_DEBUG_STUFF
		for (size_t taskIdx = 0; taskIdx < reachableTasks.size (); ++taskIdx)
		{
			const GroundedTask & task = reachableTasks[taskIdx];
			assert (task.groundedNo == taskIdx);
			std::cerr << "    Task " << taskIdx << " " << domain.tasks[task.taskNo].name << " (" << task.groundedNo << ", " << ((task.taskNo < domain.nPrimitiveTasks) ? "primitive" : " abstract") << "): " << unfulfilledPreconditions[task.groundedNo] << " unfulfilled preconditions." << std::endl;
		}
#endif

		remainingFactsCount = reachedFactsCount;

		if (reachedTasksCount == remainingPrimitiveTasks && !alwaysRunDFS)
			break;

		alwaysRunDFS = false;

		remainingPrimitiveTasks = reachedTasksCount;
	
		DEBUG(for (int i = 0; i < reachableMethods.size(); i++){
			if (prunedMethods[i]) continue;
			assert(!prunedTasks[reachableMethods[i].groundedAddEffects[0]]);
		});


		// Do grounded TDG
		std::vector<bool> taskReached;
		auto [reachedMethodsCount, reachedTasksCountTdg] = groundedTdg (taskReached, unfulfilledPreconditions, prunedMethods, prunedTasks, reachableMethods, reachableTasks, domain, problem);
		if (!config.quietMode) std::cerr << "Grounded TDG:" << std::endl;
		if (!config.quietMode) std::cerr << "Input was [" << remainingMethodsCount << ", " << remainingPrimitiveTasks << "], output was [" << reachedMethodsCount << ", " << reachedTasksCountTdg << "]." << std::endl;
	
		DEBUG(for (int i = 0; i < reachableMethods.size(); i++){
			if (prunedMethods[i]) continue;
			assert(!prunedTasks[reachableMethods[i].groundedAddEffects[0]]);
		});


		// Do DFS
		auto [reachedPrimitiveTasksCountDfs, reachedMethodsCountDfs] = groundedTdgDfs (prunedTasks, prunedMethods, reachableTasks, reachableMethods, domain, problem);

		DEBUG(for (int i = 0; i < reachableMethods.size(); i++){
			if (prunedMethods[i]) continue;	

			if (prunedTasks[reachableMethods[i].groundedAddEffects[0]]){
				std::cout << "Method " << i << " " << reachableMethods[i].groundedAddEffects[0] << std::endl;
			}
			assert(!prunedTasks[reachableMethods[i].groundedAddEffects[0]]);
		});



		// set this early
		remainingMethodsCount = reachedMethodsCountDfs;
		
		if (reachedPrimitiveTasksCountDfs == remainingPrimitiveTasks)
			break;

		remainingPrimitiveTasks = reachedPrimitiveTasksCountDfs;
	}


	return;
}
