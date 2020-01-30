#include "gpg.h"

#include "postprocessing.h"
#include "groundedGPG.h"

std::map<int,int> liftedGroundingCount;
size_t totalFactTests = 0;
std::vector<std::vector<std::vector<size_t>>> factTests;
size_t totalFactHits = 0;
std::vector<std::vector<std::vector<size_t>>> factHits;
std::vector<std::vector<std::vector<size_t>>> factFutureRejects;

std::vector<size_t> futureReject;
std::vector<size_t> futureTests;
std::vector<size_t> htReject;
std::vector<size_t> htTests;



// Returns the new number of the visited grounded task
int innerTdgDfs (std::vector<GroundedTask> & outputTasks, std::vector<GroundedMethod> & outputMethods, const std::vector<GroundedTask> & inputTasks, const std::vector<GroundedMethod> & inputMethods, const Domain & domain, std::vector<int> & visitedTasks, size_t groundedTaskIdx)
{
	if (visitedTasks[groundedTaskIdx] != -1)
		return visitedTasks[groundedTaskIdx];

	const GroundedTask & groundedTask = inputTasks[groundedTaskIdx];

	// Copy and renumber the grounded task
	int newTaskNo = outputTasks.size ();
	GroundedTask taskCopy = groundedTask;
	taskCopy.groundedNo = newTaskNo;
	outputTasks.push_back (taskCopy);

	visitedTasks[groundedTaskIdx] = newTaskNo;

	//for (auto groundedMethodIdx : groundedTask.groundedDecompositionMethods)
	for (size_t groundedMethodIdx = 0; groundedMethodIdx < groundedTask.groundedDecompositionMethods.size (); ++groundedMethodIdx)
	{
		int groundedMethodNo = groundedTask.groundedDecompositionMethods[groundedMethodIdx];
		const GroundedMethod & groundedMethod = inputMethods[groundedMethodNo];

		// Copy and renumber the grounded method
		int newMethodNo = outputMethods.size ();
		GroundedMethod methodCopy = groundedMethod;
		methodCopy.groundedNo = newMethodNo;

		outputTasks[newTaskNo].groundedDecompositionMethods[groundedMethodIdx] = newMethodNo;

		methodCopy.groundedAddEffects.clear ();
		methodCopy.groundedAddEffects.push_back (newTaskNo);

		outputMethods.push_back (methodCopy);

		for (size_t subtaskIdx = 0; subtaskIdx < groundedMethod.groundedPreconditions.size (); ++subtaskIdx)
		{
			int subtaskNo = groundedMethod.groundedPreconditions[subtaskIdx];
			int newSubtaskNo = innerTdgDfs (outputTasks, outputMethods, inputTasks, inputMethods, domain, visitedTasks, subtaskNo);
			outputMethods[newMethodNo].groundedPreconditions[subtaskIdx] = newSubtaskNo;
		}
	}

	return newTaskNo;
}

void tdgDfs (std::vector<GroundedTask> & outputTasks, std::vector<GroundedMethod> & outputMethods, std::vector<GroundedTask> & inputTasks, const std::vector<GroundedMethod> & inputMethods, const Domain & domain, const Problem & problem)
{
	std::vector<int> visitedTasks (inputTasks.size (), -1);

	for (const GroundedTask & task : inputTasks)
	{
		if (task.taskNo != problem.initialAbstractTask)
			continue;
		innerTdgDfs (outputTasks, outputMethods, inputTasks, inputMethods, domain, visitedTasks, task.groundedNo);
	}
}




