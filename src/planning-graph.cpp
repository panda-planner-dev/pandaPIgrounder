#include <algorithm>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <vector>

#include <cassert>

#include "debug.h"
#include "model.h"
#include "planning-graph.h"

static void assignVariables (std::vector<GroundedTask> & output, std::set<Fact> & newFacts, const std::set<Fact> & knownFacts, const Domain & domain, int taskNo, std::map<int, int> & assignedVariables, size_t variableIdx = 0)
{
	const Task & task = domain.tasks[taskNo];

	assert (taskNo < domain.nPrimitiveTasks);

	if (variableIdx >= task.variableSorts.size ())
		assert (assignedVariables.size () == task.variableSorts.size ());

	if (assignedVariables.size () == task.variableSorts.size ())
	{
		// All variables assigned!

		DEBUG (
			// Count unassigned variables
			size_t unassigned = 0;
			for (size_t varIdx = 0; varIdx < task.variableSorts.size (); ++varIdx)
			{
				if (assignedVariables.count (varIdx) == 0)
					++unassigned;
			}
			assert (unassigned == task.variableSorts.size () - assignedVariables.size ());
			assert (unassigned == 0);
		);

		// Check variable constraints
		for (const VariableConstraint & constraint : domain.tasks[taskNo].variableConstraints)
		{
			int val1 = assignedVariables[constraint.var1];
			int val2 = assignedVariables[constraint.var2];
			if (constraint.type == VariableConstraint::Type::EQUAL)
			{
				if (val1 != val2)
					return;
			}
			else if (constraint.type == VariableConstraint::Type::NOT_EQUAL)
			{
				if (val1 == val2)
					return;
			}
		}

		DEBUG (
			std::cerr << "Found grounded task for task [" << task.name << "] with [" << unassigned << "] unassigned variables." << std::endl;
			/*
			std::cerr << "Assigned variables:" << std::endl;
			for (auto assignedVar : assignedVariables)
			{
				std::cerr << "Variable " << assignedVar.first << " (" << domain.sorts[task.variableSorts[assignedVar.first]].name << ") = " << assignedVar.second << " (" << domain.constants[assignedVar.second] << ")" << std::endl;
			}
			*/
		);

		// Create and return grounded task
		GroundedTask groundedTask;
		groundedTask.taskNo = taskNo;
		groundedTask.arguments.resize (task.variableSorts.size ());
		for (size_t varIdx = 0; varIdx < task.variableSorts.size (); ++varIdx)
		{
			assert (assignedVariables.count (varIdx) > 0);
			groundedTask.arguments[varIdx] = assignedVariables[varIdx];
		}
		output.push_back (groundedTask);

		// Add "add" effects from this task to our known facts
		for (const PredicateWithArguments & addEffect : task.effectsAdd)
		{
			Fact addFact;
			addFact.predicateNo = addEffect.predicateNo;
			for (int varIdx : addEffect.arguments)
			{
				assert (assignedVariables.count (varIdx) > 0);
				addFact.arguments.push_back (assignedVariables[varIdx]);
			}

			// If we already processed this fact, don't add it again
			if (knownFacts.count (addFact) == 0)
				newFacts.insert (addFact);
		}

		return;
	}

	if (assignedVariables.count (variableIdx) > 0)
	{
		// Variable is already assigned
		assignVariables (output, newFacts, knownFacts, domain, taskNo, assignedVariables, variableIdx + 1);
		return;
	}

	int variableSort = task.variableSorts[variableIdx];
	for (int sortMember : domain.sorts[variableSort].members)
	{
		assignedVariables[variableIdx] = sortMember;
		assignVariables (output, newFacts, knownFacts, domain, taskNo, assignedVariables, variableIdx + 1);
	}
	assignedVariables.erase (variableIdx);
}

static void matchPrecondition (std::vector<GroundedTask> & output, std::set<Fact> & newFacts, const std::set<Fact> & knownFacts, const Domain & domain, size_t taskNo, std::map<int, int> & assignedVariables, size_t initiallyMatchedPrecondition, const Fact & initiallyMatchedFact, size_t preconditionIdx = 0)
{
	const Task & task = domain.tasks[taskNo];

	if (preconditionIdx >= task.preconditions.size ())
	{
		// Processed all preconditions. This is a potentially reachable ground instance.
		// Now we only need to assign all unassigned variables.
		assignVariables (output, newFacts, knownFacts, domain, taskNo, assignedVariables);

		return;
	}

	// Skip initially matched precondition
	if (preconditionIdx == initiallyMatchedPrecondition)
	{
		matchPrecondition (output, newFacts, knownFacts, domain, taskNo, assignedVariables, initiallyMatchedPrecondition, initiallyMatchedFact, preconditionIdx + 1);
		return;
	}

	const PredicateWithArguments & precondition = task.preconditions[preconditionIdx];

	// Try to find a fact that fulfills this precondition
	bool foundMatchingFact = false;
	for (const Fact & fact : knownFacts)
	{
		// Necessary for duplicate elemination. If an action has two preconditions to which the initiallyMatchedFact can be matched, we would generate some groundings twice.
		// The currently *new* initiallyMatchedFact can only be matched to preconditions before the precondition to which it was matched to start this grounding.
		if (preconditionIdx >= initiallyMatchedPrecondition && fact == initiallyMatchedFact)
			continue;

		if (fact.predicateNo != precondition.predicateNo)
			continue;

		assert (fact.arguments.size () == precondition.arguments.size ());
		VariableAssignment assignedVariablesBefore = assignedVariables;
		bool factMatches = true;
		for (size_t argIdx = 0; argIdx < precondition.arguments.size (); ++argIdx)
		{
			int taskVarIdx = precondition.arguments[argIdx];
			int factArgument = fact.arguments[argIdx];

			if (assignedVariables.count (taskVarIdx) == 0)
			{
				// Variable is not assigned yet
				int taskArgIdx = precondition.arguments[argIdx];
				int argumentSort = task.variableSorts[taskArgIdx];
				if (domain.sorts[argumentSort].members.count (fact.arguments[argIdx]) == 0)
				{
					factMatches = false;
					break;
				}

				assignedVariables[taskVarIdx] = factArgument;
			}
			else if (assignedVariables[taskVarIdx] == factArgument)
			{
				// Variable is assigned, and the assigned constant matches the fact
			}
			else
			{
				// Variable is assigned, but the assigned constant does not match the fact
				factMatches = false;
				break;
			}
		}

		if (factMatches)
		{
			foundMatchingFact = true;
			matchPrecondition (output, newFacts, knownFacts, domain, taskNo, assignedVariables, initiallyMatchedPrecondition, initiallyMatchedFact, preconditionIdx + 1);
		}

		assignedVariables = assignedVariablesBefore;
	}

	if (!foundMatchingFact)
	{
		DEBUG (std::cerr << "Unable to satisfy precondition [" << domain.predicates[precondition.predicateNo].name << "]." << std::endl);
	}
}

void runPlanningGraph (std::vector<GroundedTask> & outputTasks, std::set<Fact> & outputFacts, const Domain & domain, const Problem & problem)
{
	outputTasks.clear ();
	outputFacts.clear ();

	std::set<Fact> processedFacts;
	std::set<Fact> toBeProcessed;

	// Consider all facts from the initial state as not processed yet
	for (const Fact & initFact : problem.init)
		toBeProcessed.insert (initFact);

	// First, process all tasks without preconditions
	for (int taskIdx = 0; taskIdx < domain.nPrimitiveTasks; ++taskIdx)
	{
		const Task & task = domain.tasks[taskIdx];
		if (task.preconditions.size () != 0)
			continue;

		VariableAssignment assignedVariables;
		Fact f;
		matchPrecondition (outputTasks, toBeProcessed, processedFacts, domain, taskIdx, assignedVariables, 0, f);
	}

	while (!toBeProcessed.empty ())
	{
		// Take any not-yet-processed fact
		auto it = toBeProcessed.begin ();
		const Fact fact = *it;
		toBeProcessed.erase (it);
		processedFacts.insert (fact);

		DEBUG (std::cerr << "Processing fact:" << std::endl);
		DEBUG (printFact (domain, fact));

		// Find tasks with this predicate as precondition
		for (int taskIdx = 0; taskIdx < domain.nPrimitiveTasks; ++taskIdx)
		{
			const Task & task = domain.tasks[taskIdx];
			for (size_t preconditionIdx = 0; preconditionIdx < task.preconditions.size (); ++preconditionIdx)
			{
				VariableAssignment assignedVariables;
				if (!task.doesFactFulfilPrecondition (&assignedVariables, domain, fact, preconditionIdx))
					continue;

				DEBUG (std::cerr << "Fact fulfils precondition " << preconditionIdx << " of task:" << std::endl);
				DEBUG (printTask (domain, task));

				matchPrecondition (outputTasks, toBeProcessed, processedFacts, domain, taskIdx, assignedVariables, preconditionIdx, fact);
			}
		}

		DEBUG (std::cerr << std::endl);
	}

	outputFacts = processedFacts;

	DEBUG (std::cerr << "[" << processedFacts.size () << "] facts are potentially reachable." << std::endl);
}

void doAndPrintPlanningGraph (const Domain & domain, const Problem & problem)
{
	std::vector<GroundedTask> groundedTasks;
	std::set<Fact> reachableFacts;
	runPlanningGraph (groundedTasks, reachableFacts, domain, problem);
	DEBUG (std::cerr << "Calculated [" << groundedTasks.size () << "] grounded tasks." << std::endl);

	// Output
	std::cout << groundedTasks.size () << " " << reachableFacts.size () << std::endl;

	// Helper vector for sorting the output
	std::vector<std::string> sortVec;

	// First print all grounded tasks
	sortVec.clear ();
	for (const GroundedTask & groundedTask : groundedTasks)
	{
		std::stringstream stream;
		stream << domain.tasks[groundedTask.taskNo].name;
		for (int argument : groundedTask.arguments)
			stream << " " << domain.constants[argument];

		sortVec.push_back (stream.str ());
	}

	sort (sortVec.begin (), sortVec.end ());
	for (const std::string & str : sortVec)
		std::cout << str << std::endl;

	// Then print all reachable facts
	sortVec.clear ();
	for (const Fact & fact : reachableFacts)
	{
		std::stringstream stream;
		stream << domain.predicates[fact.predicateNo].name;
		for (int argument : fact.arguments)
			stream << " " << domain.constants[argument];

		sortVec.push_back (stream.str ());
	}

	sort (sortVec.begin (), sortVec.end ());
	for (const std::string & str : sortVec)
		std::cout << str << std::endl;
}
