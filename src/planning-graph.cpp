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

/**
 * @brief Contains a reference to a domain, and other useful information that speeds up the grounding process.
 */
struct PreprocessedDomain
{
	/**
	 * @brief The original domain.
	 */
	const Domain & domain;

	/**
	 * @brief A set containing all variables that are already assigned when a precondition is processed.
	 *
	 * Preconditions are processed in order by matchPrecondition(). This means that when we are looking for
	 * a Fact to fulfill precondition \f$i\f$, the variables used in preconditions \f$[0; i)\f$ have already been assigned.
	 *
	 * This allows us to efficiently find Facts that could potentially satisfy a precondition.
	 */
	std::vector<std::vector<std::set<int>>> assignedVariablesByTaskAndPrecondition;

	/**
	 * @brief A list of tasks and preconditions for each predicate.
	 *
	 * For each predicate, we have a list of pairs. In the pair, the first member is the number of the task,
	 * and the second member is the index of the precondition that uses the corresponding predicate.
	 */
	std::vector<std::vector<std::pair<int, int>>> preconditionsByPredicate;

	/**
	 * @brief Preprocesses the given Domain.
	 */
	PreprocessedDomain (const Domain & domain);
};

PreprocessedDomain::PreprocessedDomain (const Domain & domain) : domain (domain)
{
	assignedVariablesByTaskAndPrecondition.resize (domain.nPrimitiveTasks);
	preconditionsByPredicate.resize (domain.predicates.size ());

	for (size_t taskIdx = 0; taskIdx < domain.nPrimitiveTasks; ++taskIdx)
	{
		const Task & task = domain.tasks[taskIdx];

		assignedVariablesByTaskAndPrecondition[taskIdx].resize (task.preconditions.size ());

		std::set<int> alreadyAssignedVariables;
		for (size_t preconditionIdx = 0; preconditionIdx < task.preconditions.size (); ++preconditionIdx)
		{
			// Calculate which variables are assigned when a precondition is matched
			assignedVariablesByTaskAndPrecondition[taskIdx][preconditionIdx].insert (alreadyAssignedVariables.begin (), alreadyAssignedVariables.end ());
			const PredicateWithArguments & precondition = task.preconditions[preconditionIdx];
			for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
			{
				int variable = precondition.arguments[argumentIdx];
				alreadyAssignedVariables.insert (variable);
			}

			// Group preconditions by predicate
			preconditionsByPredicate[precondition.predicateNo].push_back (std::make_pair (taskIdx, preconditionIdx));
		}
	}
}

/**
 * @brief Allows efficient access to Facts that could potentially satisfy a precondition.
 */
struct PreconditionFactMap
{
	using VariablesToFactListMap = std::map<std::vector<int>, std::vector<Fact>>;

	/**
	 * @brief The preprocessed domain.
	 */
	const PreprocessedDomain & preprocessedDomain;

	/**
	 * @brief A list of Facts for each task, precondition and set of assigned variables.
	 */
	std::vector<std::vector<VariablesToFactListMap>> factMap;

	/**
	 * @brief Initializes the factMap.
	 */
	PreconditionFactMap (const PreprocessedDomain & preprocessedDomain);

	/**
	 * @brief Inserts a Fact into the maps of all preconditions with the same predicate as the Fact.
	 */
	void insertFact (const Fact & fact);

	/**
	 * @brief Returns all Facts for the given precondition in the given task that are compatible with the given variable assignment.
	 */
	std::vector<Fact> getFacts (size_t taskNo, size_t preconditionIdx, const VariableAssignment & assignedVariables) const;
};

PreconditionFactMap::PreconditionFactMap (const PreprocessedDomain & preprocessedDomain) : preprocessedDomain (preprocessedDomain)
{
	factMap.resize (preprocessedDomain.domain.nPrimitiveTasks);

	for (size_t taskIdx = 0; taskIdx < preprocessedDomain.domain.nPrimitiveTasks; ++taskIdx)
	{
		const Task & task = preprocessedDomain.domain.tasks[taskIdx];
		factMap[taskIdx].resize (task.preconditions.size ());
	}
}

void PreconditionFactMap::insertFact (const Fact & fact)
{
	DEBUG (std::cerr << "Inserting fact:" << std::endl; printFact (preprocessedDomain.domain, fact));

	for (const auto & [taskNo, preconditionIdx] : preprocessedDomain.preconditionsByPredicate[fact.predicateNo])
	{
		const Task & task = preprocessedDomain.domain.tasks[taskNo];
		const PredicateWithArguments & precondition = task.preconditions[preconditionIdx];

		assert (precondition.arguments.size () == fact.arguments.size ());

		std::vector<int> values;
		for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
		{
			int var = precondition.arguments[argumentIdx];
			if (preprocessedDomain.assignedVariablesByTaskAndPrecondition[taskNo][preconditionIdx].count (var) > 0)
			{
				values.push_back (fact.arguments[argumentIdx]);
			}
		}

		factMap[taskNo][preconditionIdx][values].push_back (fact);
	}
}

std::vector<Fact> PreconditionFactMap::getFacts (size_t taskNo, size_t preconditionIdx, const VariableAssignment & assignedVariables) const
{
	const PredicateWithArguments & precondition = preprocessedDomain.domain.tasks[taskNo].preconditions[preconditionIdx];

	// Build the vector which is used as the key in the map
	std::vector<int> assignedVariableValues;
	for (size_t argIdx = 0; argIdx < precondition.arguments.size (); ++argIdx)
	{
		int var = precondition.arguments[argIdx];
		if (!(preprocessedDomain.assignedVariablesByTaskAndPrecondition[taskNo][preconditionIdx].count (var) > 0))
			continue;

		assert (assignedVariables.isAssigned (var));
		assignedVariableValues.push_back (assignedVariables[var]);
	}

	// The map itself is guaranteed to exist (it was created in the constructor), but the entry matching the assigned variables may not exist.
	const auto & map = factMap.at (taskNo).at (preconditionIdx);
	if (map.count (assignedVariableValues) == 0)
		return std::vector<Fact> ();
	return map.at (assignedVariableValues);
}

static void assignVariables (std::vector<GroundedTask> & output, std::set<Fact> & newFacts, const FactSet & knownFacts, const Domain & domain, int taskNo, VariableAssignment & assignedVariables, size_t variableIdx = 0)
{
	const Task & task = domain.tasks[taskNo];

	assert (taskNo < domain.nPrimitiveTasks);

	if (variableIdx >= task.variableSorts.size ())
		assert (assignedVariables.size () == task.variableSorts.size ());

	if (assignedVariables.size () == task.variableSorts.size ())
	{
		// All variables assigned!

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
			std::cerr << "Found grounded task for task [" << task.name << "]." << std::endl;
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
		groundedTask.arguments = assignedVariables;
		output.push_back (groundedTask);

		// Add "add" effects from this task to our known facts
		for (const PredicateWithArguments & addEffect : task.effectsAdd)
		{
			Fact addFact;
			addFact.predicateNo = addEffect.predicateNo;
			for (int varIdx : addEffect.arguments)
			{
				assert (assignedVariables.isAssigned (varIdx));
				addFact.arguments.push_back (assignedVariables[varIdx]);
			}

			// If we already processed this fact, don't add it again
			if (knownFacts.count (addFact) == 0)
				newFacts.insert (addFact);
		}

		return;
	}

	if (assignedVariables.isAssigned (variableIdx))
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

static void matchPrecondition (std::vector<GroundedTask> & output, std::set<Fact> & newFacts, const FactSet & knownFacts, const PreconditionFactMap & factMap, const PreprocessedDomain & preprocessedDomain, size_t taskNo, VariableAssignment & assignedVariables, size_t initiallyMatchedPrecondition, const Fact & initiallyMatchedFact, size_t preconditionIdx = 0)
{
	const Task & task = preprocessedDomain.domain.tasks[taskNo];

	if (preconditionIdx >= task.preconditions.size ())
	{
		// Processed all preconditions. This is a potentially reachable ground instance.
		// Now we only need to assign all unassigned variables.
		assignVariables (output, newFacts, knownFacts, preprocessedDomain.domain, taskNo, assignedVariables);

		return;
	}

	// Skip initially matched precondition
	if (preconditionIdx == initiallyMatchedPrecondition)
	{
		matchPrecondition (output, newFacts, knownFacts, factMap, preprocessedDomain, taskNo, assignedVariables, initiallyMatchedPrecondition, initiallyMatchedFact, preconditionIdx + 1);
		return;
	}

	const PredicateWithArguments & precondition = task.preconditions[preconditionIdx];

	// Try to find a fact that fulfills this precondition
	bool foundMatchingFact = false;
	for (const Fact & fact : factMap.getFacts (taskNo, preconditionIdx, assignedVariables))
	{
		// Necessary for duplicate elemination. If an action has two preconditions to which the initiallyMatchedFact can be matched, we would generate some groundings twice.
		// The currently *new* initiallyMatchedFact can only be matched to preconditions before the precondition to which it was matched to start this grounding.
		if (preconditionIdx >= initiallyMatchedPrecondition && fact == initiallyMatchedFact)
			continue;

		assert (fact.predicateNo == precondition.predicateNo);
		assert (fact.arguments.size () == precondition.arguments.size ());
		std::set<int> newlyAssigned;
		bool factMatches = true;
		for (size_t argIdx = 0; argIdx < precondition.arguments.size (); ++argIdx)
		{
			int taskVarIdx = precondition.arguments[argIdx];
			int factArgument = fact.arguments[argIdx];

			if (!assignedVariables.isAssigned (taskVarIdx))
			{
				// Variable is not assigned yet
				int taskArgIdx = precondition.arguments[argIdx];
				int argumentSort = task.variableSorts[taskArgIdx];
				if (preprocessedDomain.domain.sorts[argumentSort].members.count (fact.arguments[argIdx]) == 0)
				{
					factMatches = false;
					break;
				}

				newlyAssigned.insert (taskVarIdx);
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
			matchPrecondition (output, newFacts, knownFacts, factMap, preprocessedDomain, taskNo, assignedVariables, initiallyMatchedPrecondition, initiallyMatchedFact, preconditionIdx + 1);
		}

		for (int newlyAssignedVar : newlyAssigned)
			assignedVariables.erase (newlyAssignedVar);
	}

	if (!foundMatchingFact)
	{
		DEBUG (std::cerr << "Unable to satisfy precondition [" << domain.predicates[precondition.predicateNo].name << "]." << std::endl);
	}
}

void runPlanningGraph (std::vector<GroundedTask> & outputTasks, std::set<Fact> & outputFacts, const Domain & domain, const Problem & problem)
{
	outputTasks.clear ();

	PreprocessedDomain preprocessedDomain (domain);

	FactSet processedFacts (domain.predicates.size ());
	std::set<Fact> toBeProcessed;
	PreconditionFactMap factMap (preprocessedDomain);

	// Consider all facts from the initial state as not processed yet
	for (const Fact & initFact : problem.init)
		toBeProcessed.insert (initFact);

	// First, process all tasks without preconditions
	for (int taskIdx = 0; taskIdx < domain.nPrimitiveTasks; ++taskIdx)
	{
		const Task & task = domain.tasks[taskIdx];
		if (task.preconditions.size () != 0)
			continue;

		VariableAssignment assignedVariables (task.variableSorts.size ());
		Fact f;
		matchPrecondition (outputTasks, toBeProcessed, processedFacts, factMap, preprocessedDomain, taskIdx, assignedVariables, 0, f);
	}

	while (!toBeProcessed.empty ())
	{
		// Take any not-yet-processed fact
		auto it = toBeProcessed.begin ();
		const Fact fact = *it;
		toBeProcessed.erase (it);
		factMap.insertFact (fact);
		processedFacts.insert (fact);

		DEBUG (std::cerr << "Processing fact:" << std::endl);
		DEBUG (printFact (domain, fact));

		// Find tasks with this predicate as precondition
		for (int taskIdx = 0; taskIdx < domain.nPrimitiveTasks; ++taskIdx)
		{
			const Task & task = domain.tasks[taskIdx];
			for (size_t preconditionIdx = 0; preconditionIdx < task.preconditions.size (); ++preconditionIdx)
			{
				VariableAssignment assignedVariables (task.variableSorts.size ());
				if (!task.doesFactFulfilPrecondition (&assignedVariables, domain, fact, preconditionIdx))
					continue;

				DEBUG (std::cerr << "Fact fulfils precondition " << preconditionIdx << " of task:" << std::endl);
				DEBUG (printTask (domain, task));

				matchPrecondition (outputTasks, toBeProcessed, processedFacts, factMap, preprocessedDomain, taskIdx, assignedVariables, preconditionIdx, fact);
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
