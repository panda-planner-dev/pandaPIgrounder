#ifndef GPG_H_INCLUDED
#define GPG_H_INCLUDED

/**
 * @defgroup gpg Generalized Planning Graph
 *
 * @{
 */

#include <algorithm>
#include <functional>
#include <iomanip>
#include <memory>
#include <numeric>
#include <queue>
#include <set>
#include <sstream>
#include <vector>

#include <cassert>

#include "hierarchy-typing.h"
#include "model.h"
#include "planning-graph.h"

#define TDG
#define PRINT_METHODS

template <typename T>
concept bool GpgInstance = requires (T instance)
{
	typename T::StateType;
	typename T::ActionType;
	typename T::ResultType;
	typename T::PreconditionType;

	requires Literal<typename T::StateType>;
	requires Literal<typename T::ResultType>;
	requires Literal<typename T::PreconditionType>;

	// ...other things?
};

template <Literal T>
struct GpgLiteralSet
{
	/// Contains a std::set<T> for each predicate.
	std::vector<std::set<T>> factsByPredicate;

	/**
	 * @brief Initializes the GpgLiteralSet.
	 *
	 * The nPredicates argument is the number of supported predicates. It is used as the size of the internal fact set vector.
	 */
	GpgLiteralSet (size_t nPredicates) : factsByPredicate (nPredicates) {}

	/**
	 * @brief Returns the number of all facts in the set.
	 *
	 * Has a complexity of O(n) where n is the number of predicates, but seems to be fast enough in practice.
	 */
	size_t size (void) const
	{
		return std::accumulate (factsByPredicate.begin (), factsByPredicate.end (), 0, [](const int & acc, const auto & factSet) { return acc + factSet.size (); });
	}

	/**
	 * @brief Returns 1 if the given fact is in the set, or 0 if not.
	 *
	 * It is an error to call this function with a fact where Fact.predicateNo is greater than or equal to nPredicates as passed to the constructor of this GpgLiteralSet.
	 */
	size_t count (const T & fact) const
	{
		assert (fact.getHeadNo () < factsByPredicate.size ());

		return factsByPredicate[fact.getHeadNo ()].count (fact);
	}

	/**
	 * @brief Inserts the given fact into the GpgLiteralSet.
	 *
	 * It is an error to call this function with a fact where Fact.predicateNo is greater than or equal to nPredicates as passed to the constructor of this GpgLiteralSet.
	 */
	void insert (const T & fact)
	{
		assert (fact.getHeadNo () < factsByPredicate.size ());

		factsByPredicate[fact.getHeadNo ()].insert (fact);
	}

	/**
	 * @brief Returns the set of facts for the given predicate.
	 *
	 * It is an error to call this function with a predicateNo which is greater than or equal to nPredicates as passed to the constructor of this GpgLiteralSet.
	 */
	const std::set<T> & getFactsForPredicate (int headNo) const
	{
		assert (headNo < factsByPredicate.size ());

		return factsByPredicate[headNo];
	}

	/**
	 * @brief Returns an iterator to the given fact in the set.
	 *
	 * If the given fact is not in the set, the returned iterator is equal to end(fact.getHeadNo()).
	 */
	typename std::set<T>::iterator find (const T & fact) const
	{
		return factsByPredicate[fact.getHeadNo ()].find (fact);
	}

	/**
	 * @brief Returns the end iterator for the fact set for the given predicate.
	 */
	typename std::set<T>::iterator end (int headNo) const
	{
		return factsByPredicate[headNo].end ();
	}

	/// Returns a std::set containing all facts in this GpgLiteralSet.
	operator std::set<T> (void) const
	{
		std::set<T> result;
		for (auto predicateFacts : factsByPredicate)
			result.insert (predicateFacts.begin (), predicateFacts.end ());
		return result;
	}
};

/**
 * @brief Contains a reference to a domain, and other useful information that speeds up the grounding process.
 */
template <GpgInstance InstanceType>
struct GpgPreprocessedDomain
{
	/**
	 * @brief The original domain.
	 */
	const Domain & domain;

	/**
	 * @brief A set containing all variables that are already assigned when a precondition is processed.
	 *
	 * Preconditions are processed in order by gpgMatchPrecondition(). This means that when we are looking for
	 * a Fact to fulfill precondition \f$i\f$, the variables used in preconditions \f$[0; i)\f$ have already been assigned.
	 *
	 * This allows us to efficiently find Facts that could potentially satisfy a precondition.
	 *
	 * Indexing: action index -> precondition index -> initially matched precondition index (-1 if not eligible)
	 */
	std::vector<std::vector<std::map<int, std::set<int>>>> assignedVariablesByTaskAndPrecondition;

	/**
	 * @brief A list of tasks and preconditions for each predicate.
	 *
	 * For each predicate, we have a list of pairs. In the pair, the first member is the number of the task,
	 * and the second member is the index of the precondition that uses the corresponding predicate.
	 */
	std::vector<std::vector<std::pair<int, int>>> preconditionsByPredicate;

	/**
	 * @brief A set of preconditions which can be optimized as the initially matched precondition.
	 *
	 * If the initially matched precondition of a task is contained in this set, the variables referenced in the
	 * precondition are assumed to be assigned as well, and GpgStateMap#getFacts() will only return facts that are
	 * definitely compatible with all assigned variables.
	 * If the initially matched precondition is NOT contained in this set, GpgStateMap#getFacts() might still return facts
	 * that are not compatible with the initially matched precondition (but they will be compatible with all other preconditions
	 * that were matched so far).
	 */
	std::vector<std::set<int>> eligibleInitialPreconditionsByAction;

	/**
	 * @brief Preprocesses the given Domain.
	 *
	 * If enableHierarchyTyping is given, the Hierarchy Typing will be calculated using the given Domain and Problem,
	 * and can then be used by the Planning Graph.
	 */
	GpgPreprocessedDomain (const InstanceType & instance, const Domain & domain, const Problem & problem) : domain (domain)
	{
		assignedVariablesByTaskAndPrecondition.resize (instance.getNumberOfActions ());
		preconditionsByPredicate.resize (instance.getNumberOfPredicates ());
		eligibleInitialPreconditionsByAction.resize (instance.getNumberOfActions ());

		for (size_t actionIdx = 0; actionIdx < instance.getNumberOfActions (); ++actionIdx)
		{
			const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];

			assignedVariablesByTaskAndPrecondition[actionIdx].resize (action.getAntecedents ().size ());

			// Determine which preconditions are eligible for optimization
			// FIXME
			//if (action.getAntecedents().size() < 6)
			//for (size_t preconditionIdx = 0; preconditionIdx < action.getAntecedents ().size (); ++preconditionIdx)
			//	eligibleInitialPreconditionsByAction[actionIdx].insert (preconditionIdx);

			std::set<int> alreadyAssignedVariables;
			for (size_t preconditionIdx = 0; preconditionIdx < action.getAntecedents ().size (); ++preconditionIdx)
			{
				// Calculate which variables are assigned when a precondition is matched
				assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx][-1].insert (alreadyAssignedVariables.begin (), alreadyAssignedVariables.end ());
				for (size_t initiallyMatchedPreconditionIdx : eligibleInitialPreconditionsByAction[actionIdx])
				{
					assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx][initiallyMatchedPreconditionIdx].insert (alreadyAssignedVariables.begin (), alreadyAssignedVariables.end ());

					const typename InstanceType::PreconditionType & initiallyMatchedPrecondition = action.getAntecedents ()[initiallyMatchedPreconditionIdx];
					for (size_t argumentIdx = 0; argumentIdx < initiallyMatchedPrecondition.arguments.size (); ++argumentIdx)
					{
						int variable = initiallyMatchedPrecondition.arguments[argumentIdx];
						assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx][initiallyMatchedPreconditionIdx].insert (variable);
					}
				}

				const typename InstanceType::PreconditionType & precondition = action.getAntecedents ()[preconditionIdx];
				for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
				{
					int variable = precondition.arguments[argumentIdx];
					alreadyAssignedVariables.insert (variable);
				}

				// Group antecedents by predicate
				preconditionsByPredicate[precondition.getHeadNo ()].push_back (std::make_pair (actionIdx, preconditionIdx));
			}
		}
	}
};

/**
 * @brief Allows efficient access to Facts that could potentially satisfy a precondition.
 */
template <GpgInstance InstanceType>
struct GpgStateMap
{
	using VariablesToFactListMap = std::map<std::vector<int>, std::vector<typename InstanceType::StateType>>;

	/**
	 * @brief The GPG instance.
	 */
	const InstanceType & instance;

	/**
	 * @brief The preprocessed domain.
	 */
	const GpgPreprocessedDomain<InstanceType> & preprocessedDomain;

	/**
	 * @brief A list of Facts for each task, precondition, initially matched precondition (-1 if not eligible) and set of assigned variables.
	 */
	std::vector<std::vector<std::map<int, VariablesToFactListMap>>> factMap;

	/**
	 * @brief Initializes the factMap.
	 */
	GpgStateMap (const InstanceType & instance, const GpgPreprocessedDomain<InstanceType> & preprocessedDomain) : instance (instance), preprocessedDomain (preprocessedDomain)
	{
		factMap.resize (instance.getNumberOfActions ());

		for (size_t actionIdx = 0; actionIdx < instance.getNumberOfActions (); ++actionIdx)
		{
			const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];
			factMap[actionIdx].resize (action.getAntecedents ().size ());
		}
	}

	/**
	 * @brief Inserts a Fact into the maps of all preconditions with the same predicate as the Fact.
	 */
	void insertState (const typename InstanceType::StateType & stateElement)
	{
		for (const auto & [actionIdx, preconditionIdx] : preprocessedDomain.preconditionsByPredicate[stateElement.getHeadNo ()])
		{
			const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];
			const typename InstanceType::PreconditionType & precondition = action.getAntecedents ()[preconditionIdx];

			assert (precondition.arguments.size () == stateElement.arguments.size ());

			// Ineligible initially matched precondition
			std::vector<int> values;
			for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
			{
				int var = precondition.arguments[argumentIdx];

				// Skip this fact if its variables are incompatible with the sorts defined by the action
				int value = stateElement.arguments[argumentIdx];
				if (preprocessedDomain.domain.sorts[action.variableSorts[var]].members.count (value) == 0)
					goto next_action;

				if (preprocessedDomain.assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx].at (-1).count (var) > 0)
				{
					values.push_back (stateElement.arguments[argumentIdx]);
				}
			}
			factMap[actionIdx][preconditionIdx][-1][values].push_back (stateElement);

			// Eligible initially matched preconditions
			for (int initiallyMatchedPreconditionIdx : preprocessedDomain.eligibleInitialPreconditionsByAction[actionIdx])
			{
				std::vector<int> values;
				for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
				{
					int var = precondition.arguments[argumentIdx];
					if (preprocessedDomain.assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx].at (initiallyMatchedPreconditionIdx).count (var) > 0)
					{
						values.push_back (stateElement.arguments[argumentIdx]);
					}
				}

				factMap[actionIdx][preconditionIdx][initiallyMatchedPreconditionIdx][values].push_back (stateElement);
			}

next_action:;
		}
	}

	/**
	 * @brief Returns all Facts for the given precondition in the given task that are compatible with the given variable assignment.
	 *
	 * For performance reasons, we want to return the Fact vector by reference. This means that we may have to instantiate a new
	 * Fact vector if there is none for the given variable assignment. As a result, this method cannot be declared to be const.
	 */
	std::vector<typename InstanceType::StateType> & getFacts (size_t actionIdx, size_t preconditionIdx, const VariableAssignment & assignedVariables, int initiallyMatchedPreconditionIdx)
	{
		const typename InstanceType::PreconditionType & precondition = instance.getAllActions ()[actionIdx].getAntecedents ()[preconditionIdx];

		bool initiallyMatchedPreconditionIsEligible = preprocessedDomain.eligibleInitialPreconditionsByAction[actionIdx].count (initiallyMatchedPreconditionIdx) > 0;
		if (!initiallyMatchedPreconditionIsEligible)
			initiallyMatchedPreconditionIdx = -1;

		// Build the vector which is used as the key in the map
		std::vector<int> assignedVariableValues;
		for (size_t argIdx = 0; argIdx < precondition.arguments.size (); ++argIdx)
		{
			int var = precondition.arguments[argIdx];
			if (!(preprocessedDomain.assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx].at (initiallyMatchedPreconditionIdx).count (var) > 0))
				continue;

			assert (assignedVariables.isAssigned (var));
			assignedVariableValues.push_back (assignedVariables[var]);
		}

		return factMap[actionIdx][preconditionIdx][initiallyMatchedPreconditionIdx][assignedVariableValues];
	}
};

/**
 * @brief TODO
 */
struct GpgPlanningGraph
{
	using StateType = Fact;
	using ActionType = Task;
	using ResultType = GroundedTask;
	using PreconditionType = PredicateWithArguments;

	const Domain & domain;

	const Problem & problem;

	GpgPlanningGraph (const Domain & domain, const Problem & problem) : domain (domain), problem (problem) {}

	const std::vector<StateType> & getInitialState (void) const
	{
		return problem.init;
	}

	size_t getNumberOfActions (void) const
	{
		return domain.nPrimitiveTasks;
	}

	size_t getNumberOfPredicates (void) const
	{
		return domain.predicates.size ();
	}

	const std::vector<ActionType> & getAllActions (void) const
	{
		return domain.tasks;
	}

	bool doesStateFulfillPrecondition (const ActionType & task, VariableAssignment * assignedVariables, const StateType & fact, size_t preconditionIdx) const
	{
		return task.doesFactFulfilPrecondition (assignedVariables, domain, fact, preconditionIdx);
	}
};

template <GpgInstance InstanceType>
static void gpgAssignVariables (
	const InstanceType & instance,
	const HierarchyTyping * hierarchyTyping,
	std::vector<typename InstanceType::ResultType> & output,
	std::queue<typename InstanceType::StateType> & toBeProcessedQueue,
	std::set<typename InstanceType::StateType> & toBeProcessedSet,
	const GpgLiteralSet<typename InstanceType::StateType> & processedStates,
	int actionNo,
	VariableAssignment & assignedVariables,
	std::vector<int> & matchedPreconditions,
	size_t variableIdx = 0
)
{
	const Domain & domain = instance.domain;
	const typename InstanceType::ActionType action = instance.getAllActions ()[actionNo];

	assert (actionNo < instance.getNumberOfActions ());

	if (variableIdx >= action.variableSorts.size ())
		assert (assignedVariables.size () == action.variableSorts.size ());

	if (assignedVariables.size () == action.variableSorts.size ())
	{
		// All variables assigned!

		// Check variable constraints
		for (const VariableConstraint & constraint : action.variableConstraints)
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

		// Abort if the assigned variables are not compatible with the hierarchy typing
		if (hierarchyTyping != nullptr && !hierarchyTyping->isAssignmentCompatible<typename InstanceType::ActionType> (actionNo, assignedVariables))
			return;

		DEBUG (std::cerr << "Found grounded action for action [" << action.name << "]." << std::endl);

		// Create and return grounded action
		typename InstanceType::ResultType result;
		result.groundedNo = output.size ();
		result.setHeadNo (actionNo);
		result.arguments = assignedVariables;

		// XXX TODO: insert vector as subtasks of result
		// XXX TODO: insert ground preconditions and add effects
		result.groundedPreconditions = matchedPreconditions;
		// Still anything TODO?

		// Add "add" effects from this action to our known facts
		for (const typename InstanceType::PreconditionType addEffect : action.getConsequences ())
		{
			typename InstanceType::StateType addState;
			addState.setHeadNo (addEffect.getHeadNo ());
			for (int varIdx : addEffect.arguments)
			{
				assert (assignedVariables.isAssigned (varIdx));
				addState.arguments.push_back (assignedVariables[varIdx]);
			}

			// Check if we already know this fact
			bool found = false;
			typename std::set<typename InstanceType::StateType>::iterator factIt;
			if ((factIt = processedStates.find (addState)) != processedStates.end (addEffect.getHeadNo ()))
			{
				addState = *factIt;
				found = true;
			}
			else if ((factIt = toBeProcessedSet.find (addState)) != toBeProcessedSet.end ())
			{
				addState = *factIt;
				found = true;
			}

			// If we already processed this fact, don't add it again
			if (!found)
			{
				// New state element; give it a number
				addState.groundedNo = processedStates.size () + toBeProcessedSet.size ();

				toBeProcessedQueue.push (addState);
				toBeProcessedSet.insert (addState);
			}

			// Add this add effect to the list of add effects of the result we created
			result.groundedAddEffects.push_back (addState.groundedNo);
		}

		output.push_back (result);

		return;
	}

	if (assignedVariables.isAssigned (variableIdx))
	{
		// Variable is already assigned
		gpgAssignVariables (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStates, actionNo, assignedVariables, matchedPreconditions, variableIdx + 1);
		return;
	}

	int variableSort = action.variableSorts[variableIdx];
	for (int sortMember : domain.sorts[variableSort].members)
	{
		assignedVariables[variableIdx] = sortMember;
		gpgAssignVariables (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStates, actionNo, assignedVariables, matchedPreconditions, variableIdx + 1);
	}
	assignedVariables.erase (variableIdx);
}

size_t totalFactTests = 0;
std::vector<std::vector<size_t>> factTests;
size_t totalFactHits = 0;
std::vector<std::vector<size_t>> factHits;

template<GpgInstance InstanceType>
void gpgMatchPrecondition (
	const InstanceType & instance,
	const HierarchyTyping * hierarchyTyping,
	std::vector<typename InstanceType::ResultType> & output,
	std::queue<typename InstanceType::StateType> & toBeProcessedQueue,
	std::set<typename InstanceType::StateType> & toBeProcessedSet,
	const GpgLiteralSet<typename InstanceType::StateType> & processedStates,
	GpgStateMap<InstanceType> & stateMap,
	size_t actionNo,
	VariableAssignment & assignedVariables,
	size_t initiallyMatchedPrecondition,
	const typename InstanceType::StateType & initiallyMatchedState,
	std::vector<int> & matchedPreconditions,
	size_t preconditionIdx = 0
)
{
	const typename InstanceType::ActionType & action = instance.getAllActions ()[actionNo];

	if (preconditionIdx >= action.getAntecedents ().size ())
	{
		// Processed all preconditions. This is a potentially reachable ground instance.
		// Now we only need to assign all unassigned variables.
		gpgAssignVariables (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStates, actionNo, assignedVariables, matchedPreconditions);

		return;
	}

	// Skip initially matched precondition
	if (preconditionIdx == initiallyMatchedPrecondition)
	{
		gpgMatchPrecondition (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStates, stateMap, actionNo, assignedVariables, initiallyMatchedPrecondition, initiallyMatchedState, matchedPreconditions, preconditionIdx + 1);
		return;
	}

	const typename InstanceType::PreconditionType & precondition = action.getAntecedents ()[preconditionIdx];

	// Try to find a fact that fulfills this precondition
	for (const typename InstanceType::StateType & stateElement : stateMap.getFacts (actionNo, preconditionIdx, assignedVariables, initiallyMatchedPrecondition))
	{
		// Necessary for duplicate elimination. If an action has two preconditions to which the initiallyMatchedState can be matched, we would generate some groundings twice.
		// The currently *new* initiallyMatchedState can only be matched to preconditions before the precondition to which it was matched to start this grounding.
		if (preconditionIdx >= initiallyMatchedPrecondition && stateElement == initiallyMatchedState)
			continue;

		++totalFactTests;
		++factTests[actionNo][preconditionIdx];

		assert (stateElement.getHeadNo () == precondition.getHeadNo ());
		assert (stateElement.arguments.size () == precondition.arguments.size ());
		std::set<int> newlyAssigned;
		bool factMatches = true;
		for (size_t argIdx = 0; argIdx < precondition.arguments.size (); ++argIdx)
		{
			int taskVarIdx = precondition.arguments[argIdx];
			int factArgument = stateElement.arguments[argIdx];

			if (!assignedVariables.isAssigned (taskVarIdx))
			{
				// Variable is not assigned yet
				int taskArgIdx = precondition.arguments[argIdx];
				int argumentSort = action.variableSorts[taskArgIdx];
				if (instance.domain.sorts[argumentSort].members.count (stateElement.arguments[argIdx]) == 0)
				{
					factMatches = false;
					//std::cerr << "Sort does not match" << std::endl;
					break;
				}

				newlyAssigned.insert (taskVarIdx);
				assignedVariables[taskVarIdx] = factArgument;
			}
			else if (assignedVariables[taskVarIdx] == factArgument)
			{
				// Variable is assigned, and the assigned constant matches the stateElement
			}
			else
			{
				// Variable is assigned, but the assigned constant does not match the stateElement
				//std::cerr << "Does not match previous assignment" << std::endl;
				factMatches = false;
				break;
			}
		}

		if (factMatches)
		{
			++totalFactHits;
			++factHits[actionNo][preconditionIdx];
		}

		if (false && totalFactTests % 10000 == 0)
		{
			std::cerr << "Total fact misses: " << (totalFactTests - totalFactHits) << " / " << totalFactTests << " = " << std::fixed << std::setprecision (3) << 100.0 * (totalFactTests - totalFactHits) / totalFactTests << " % (" << totalFactHits << " hits)" << std::endl;
			for (size_t i = 0; i < instance.getNumberOfActions (); ++i)
			{
				const auto & action = instance.getAllActions ()[i];
				std::cerr << "Fact misses for action " << i << " (" << action.name << "):" << std::endl;
				for (size_t j = 0; j < action.getAntecedents ().size (); ++j)
				{
					std::cerr << "    Precondition " << (j + 1) << ": " << (factTests[i][j] - factHits[i][j]) << " / " << factTests[i][j] << " = " << std::fixed << std::setprecision (3) << 100.0 * (factTests[i][j] - factHits[i][j]) / factTests[i][j] << " % (" << factHits[i][j] << " hits)" << std::endl;
				}
			}
		}

		if (factMatches)
		{
			matchedPreconditions[preconditionIdx] = stateElement.groundedNo;
			gpgMatchPrecondition (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStates, stateMap, actionNo, assignedVariables, initiallyMatchedPrecondition, initiallyMatchedState, matchedPreconditions, preconditionIdx + 1);
		}

		for (int newlyAssignedVar : newlyAssigned)
			assignedVariables.erase (newlyAssignedVar);
	}
}

/**
 * @brief A grounded decomposition method.
 */
struct GroundedMethod
{
	/// The number of this grounded method.
	int groundedNo = -1;

	/// The number of the decomposition method.
	int methodNo;

	/// The arguments for the decomposition method.
	std::vector<int> arguments;

	/// List of grounded preconditions (subtasks)
	std::vector<int> groundedPreconditions;

	/// List of grounded add effects (exactly one abstract task)
	std::vector<int> groundedAddEffects;

	void setHeadNo (int headNo)
	{
		methodNo = headNo;
	}

	int getHeadNo (void) const
	{
		return methodNo;
	}

	bool operator < (const GroundedMethod & other) const
	{
		return std::tie (methodNo, arguments) < std::tie (other.methodNo, other.arguments);
	}

	bool operator == (const GroundedMethod & other) const
	{
		return std::tie (methodNo, arguments) == std::tie (other.methodNo, other.arguments);
	}
};

struct GpgTdg
{
	using StateType = GroundedTask;
	using ActionType = DecompositionMethod;
	using ResultType = GroundedMethod;
	using PreconditionType = TaskWithArguments;

	const Domain & domain;

	const Problem & problem;

	const std::vector<GroundedTask> & tasks;

	GpgTdg (const Domain & domain, const Problem & problem, const std::vector<GroundedTask> & tasks) : domain (domain), problem (problem), tasks (tasks) {}

	const std::vector<StateType> & getInitialState (void) const
	{
		return tasks;
	}

	size_t getNumberOfActions (void) const
	{
		return domain.decompositionMethods.size ();
	}

	size_t getNumberOfPredicates (void) const
	{
		return domain.nTotalTasks;
	}

	const std::vector<ActionType> & getAllActions (void) const
	{
		return domain.decompositionMethods;
	}

	bool doesStateFulfillPrecondition (const ActionType & method, VariableAssignment * outputVariableAssignment, const StateType & groundedTask, size_t preconditionIdx) const
	{
		const PreconditionType & precondition = method.subtasks[preconditionIdx];

		// The predicate of the fact and the precondition must match
		if (precondition.taskNo != groundedTask.taskNo)
			return false;

		assert (groundedTask.arguments.size () == domain.tasks[groundedTask.taskNo].variableSorts.size ());
		assert (groundedTask.arguments.size () == precondition.arguments.size ());

		VariableAssignment assignedVariables (method.variableSorts.size ());
		for (size_t argIdx = 0; argIdx < precondition.arguments.size (); ++argIdx)
		{
			int taskVarIdx = precondition.arguments[argIdx];
			int argumentSort = method.variableSorts[taskVarIdx];

			// Make sure that the argument to the groundedTask matches the task's variable.
			// E.g. we could have a groundedTask like "+at truck-0 city-loc-0", but this task could have
			// "+at ?var1 ?var2" as a precondition, where ?var1 must be a package (and not a truck).
			if (domain.sorts[argumentSort].members.count (groundedTask.arguments[argIdx]) == 0)
				return false;

			assignedVariables[taskVarIdx] = groundedTask.arguments[argIdx];
		}

		if (outputVariableAssignment != NULL)
			*outputVariableAssignment = assignedVariables;

		return true;
	}
};

/**
 * TODO
 */
template<GpgInstance InstanceType>
void runGpg (const InstanceType & instance, std::vector<typename InstanceType::ResultType> & output, std::set<typename InstanceType::StateType> & outputStateElements, const HierarchyTyping * hierarchyTyping)
{
	output.clear ();

	GpgPreprocessedDomain<InstanceType> preprocessed (instance, instance.domain, instance.problem);
	static GpgStateMap<InstanceType> stateMap (instance, preprocessed);

	GpgLiteralSet<typename InstanceType::StateType> processedStateElements (instance.getNumberOfPredicates ());

	// We need a queue to process new state elements in the correct order (which makes things faster),
	// and a set to prevent duplicate additions to the queue.
	std::queue<typename InstanceType::StateType> toBeProcessedQueue;
	std::set<typename InstanceType::StateType> toBeProcessedSet;

	// Consider all facts from the initial state as not processed yet
	for (typename InstanceType::StateType initStateElement : instance.getInitialState ())
	{
		// Number initial state elements
		initStateElement.groundedNo = toBeProcessedQueue.size ();

		// Filter duplicate init state elements (seems to happen in some test cases?)
		if (toBeProcessedSet.count (initStateElement) == 0)
		{
			toBeProcessedQueue.push (initStateElement);
			toBeProcessedSet.insert (initStateElement);
		}

		assert (toBeProcessedQueue.size () == toBeProcessedSet.size ());
	}

	// Reset counters
	totalFactTests = 0;
	totalFactHits = 0;

	factTests.clear ();
	factTests.resize (instance.getNumberOfActions ());
	for (size_t i = 0; i < instance.getNumberOfActions (); ++i)
		factTests[i].resize (instance.getAllActions ()[i].getAntecedents ().size ());

	factHits.clear ();
	factHits.resize (instance.getNumberOfActions ());
	for (size_t i = 0; i < instance.getNumberOfActions (); ++i)
		factHits[i].resize (instance.getAllActions ()[i].getAntecedents ().size ());

	// First, process all actions without preconditions
	for (int actionIdx = 0; actionIdx < instance.getNumberOfActions (); ++actionIdx)
	{
		const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];
		if (action.getAntecedents ().size () != 0)
			continue;

		VariableAssignment assignedVariables (action.variableSorts.size ());
		typename InstanceType::StateType f;
		std::vector<int> matchedPreconditions (action.getAntecedents ().size (), -1);
		gpgMatchPrecondition (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStateElements, stateMap, actionIdx, assignedVariables, 0, f, matchedPreconditions);
	}

	while (!toBeProcessedQueue.empty ())
	{
		assert (toBeProcessedQueue.size () == toBeProcessedSet.size ());

		// Take any not-yet-processed state element
		const typename InstanceType::StateType stateElement = toBeProcessedQueue.front ();
		toBeProcessedQueue.pop ();
		toBeProcessedSet.erase (stateElement);

		stateMap.insertState (stateElement);
		processedStateElements.insert (stateElement);

		// Find tasks with this predicate as precondition
		for (const auto & [actionIdx, preconditionIdx] : preprocessed.preconditionsByPredicate[stateElement.getHeadNo ()])
		{
			const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];

			assert (action.getAntecedents ()[preconditionIdx].getHeadNo () == stateElement.getHeadNo ());

			VariableAssignment assignedVariables (action.variableSorts.size ());
			if (!instance.doesStateFulfillPrecondition (action, &assignedVariables, stateElement, preconditionIdx))
				continue;

			std::vector<int> matchedPreconditions (action.getAntecedents ().size (), -1);
			matchedPreconditions[preconditionIdx] = stateElement.groundedNo;
			gpgMatchPrecondition (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStateElements, stateMap, actionIdx, assignedVariables, preconditionIdx, stateElement, matchedPreconditions);
		}
	}

	outputStateElements = processedStateElements;

	std::cerr << "Returning from runGpg()." << std::endl;
}

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

template <typename T>
void validateGroundedList (const std::vector<T> & input)
{
	for (size_t i = 0; i < input.size (); ++i)
	{
		if (input[i].groundedNo != i)
		{
			std::cout << "Grounded object list is inconsistent: entry " << i << " has grounded number " << input[i].groundedNo << std::endl;
			abort ();
		}
	}
}

template <typename T>
std::vector<T> renumberIf (const std::vector<T> & input, std::function<bool (const T &)> predicate)
{
	std::vector<T> result;
	result.reserve (input.size ());
	for (size_t i = 0; i < input.size (); ++i)
	{
		if (predicate (input[i]))
		{
			result.push_back (input[i]);

			// Renumber the copied item
			size_t itemIdx = result.size () - 1;
			T & item = result[itemIdx];
			item.groundedNo = itemIdx;
		}
	}
	validateGroundedList (result);
	return result;
}

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
					std::cerr << "Reached fact " << addFact << " for the first time (task without preconditions)." << std::endl;
				}
			}
		}
	}

#ifdef PRINT_DEBUG_STUFF
	std::cerr << "Before Grounded PG:" << std::endl;
	for (size_t taskIdx = 0; taskIdx < inputTasks.size (); ++taskIdx)
	{
		const GroundedTask & task = inputTasks[taskIdx];
		if (task.taskNo < domain.nPrimitiveTasks)
			std::cerr << "    Task " << taskIdx << " (" << task.groundedNo << ", primitive): " << unfulfilledPreconditions[task.groundedNo] << " vs " << domain.tasks[task.taskNo].preconditions.size () << " (unfulfilled vs preconditions), "
				<< task.groundedDecompositionMethods.size () << " grounded decomposition methods (vs " << domain.tasks[task.taskNo].decompositionMethods.size () << ")." << std::endl;
		else
			std::cerr << "    Task " << taskIdx << " (" << task.groundedNo << ",  abstract): " << unfulfilledPreconditions[task.groundedNo] << " vs " << domain.tasks[task.taskNo].preconditions.size () << " (unfulfilled vs preconditions), "
				<< task.groundedDecompositionMethods.size () << " grounded decomposition methods (vs " << domain.tasks[task.taskNo].decompositionMethods.size () << ")." << std::endl;
	}
#endif

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

#ifdef PRINT_DEBUG_STUFF
	std::cerr << "Before Grounded TDG:" << std::endl;
	for (size_t methodIdx = 0; methodIdx < inputMethods.size (); ++methodIdx)
	{
		const GroundedMethod & method = inputMethods[methodIdx];
		std::cerr << "    Method " << methodIdx << " (" << method.groundedNo << "): " << unfulfilledPreconditions[method.groundedNo] << " vs " << domain.decompositionMethods[method.methodNo].subtasks.size () << " (unfulfilled vs subtasks), "
			<< method.groundedPreconditions.size () << " grounded preconditions (vs " << domain.decompositionMethods[method.methodNo].subtasks.size () << ")." << std::endl;
		for (int subtaskNo : method.groundedPreconditions)
			std::cerr << "        Subtask " << subtaskNo << std::endl;
	}
#endif

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
		groundedInnerTdgDfs (prunedTasks, prunedMethods, inputTasks, inputMethods, domain, visitedTasks, visitedMethods, task.groundedNo);
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
			prunedTasks[taskIdx] = true;
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


void assignGroundNosToDeleteEffects(const Domain & domain, std::vector<GpgPlanningGraph::ResultType> & groundedTasksPg,std::set<GpgPlanningGraph::StateType> & reachableFacts){
	for (GpgPlanningGraph::ResultType & groundedTask : groundedTasksPg){
		// assign fact NOs to delete effects
		for (const PredicateWithArguments & delEffect : domain.tasks[groundedTask.taskNo].effectsDel){
			GpgPlanningGraph::StateType delState;
			delState.setHeadNo (delEffect.getHeadNo ());
			for (int varIdx : delEffect.arguments)
			{
				delState.arguments.push_back (groundedTask.arguments[varIdx]);
			}

			// Check if we already know this fact
			std::set<GpgPlanningGraph::StateType>::iterator factIt;
			if ((factIt = reachableFacts.find (delState)) != reachableFacts.end())
			{
				// If this delete effect occurs in the list of reachable facts, then add it to the effect list. If not, it can never be true 
				groundedTask.groundedDelEffects.push_back(factIt->groundedNo);
			}
		
		}
	}
}



void removeUnnecessaryFacts(const Domain & domain,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<GroundedTask> & inputTasksGroundedPg,
		std::vector<Fact> & inputFactsGroundedPg){

}

void expandAbstractTasksWithSingleMethod(const Domain & domain,
		const Problem & problem,
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
			
			// this method is now pruned ...
			prunedMethods[applicableIndex] = true;
			prunedTasks[groundedTask.groundedNo] = true;
	
			GroundedMethod & unitGroundedMethod = inputMethodsGroundedTdg[applicableIndex];
			DecompositionMethod unitLiftedMethod = domain.decompositionMethods[unitGroundedMethod.methodNo];
	
			// apply this method in all methods it is occurring
			DEBUG( std::cerr << "Abstract task " << groundedTask.groundedNo << " has only a single method" << std::endl);
			for (const int & method : taskToMethodsTheyAreContainedIn[groundedTask.groundedNo]){
				if (prunedMethods[method]) continue;
				DEBUG( std::cerr << "expanding in method " << method << std::endl);
				// copy the lifted method
				GroundedMethod & groundedMethod = inputMethodsGroundedTdg[method];
				DecompositionMethod liftedMethod = domain.decompositionMethods[groundedMethod.methodNo];
				
				while (true){
					bool found = false;
					for (size_t subTaskIdx = 0; subTaskIdx < liftedMethod.subtasks.size(); subTaskIdx++){
						DEBUG( std::cerr << "Checking  #" << subTaskIdx << " " << groundedMethod.groundedPreconditions[subTaskIdx] << " against " << groundedTask.groundedNo << std::endl);
						if (groundedMethod.groundedPreconditions[subTaskIdx] == groundedTask.groundedNo){
							found = true;
	
							std::vector<std::pair<int,int>> orderPertainingToThisTask;
							std::vector<std::pair<int,int>> orderNotPertainingToThisTask;
							for(auto order : liftedMethod.orderingConstraints)
								if (order.first == subTaskIdx || order.second == subTaskIdx)
									orderPertainingToThisTask.push_back(order);
								else 
									orderNotPertainingToThisTask.push_back(order);
		
							liftedMethod.name += "_applied_to_task_" + subTaskIdx + unitLiftedMethod.name + "[";
							for (unsigned int i = 0; i < unitGroundedMethod.arguments.size(); i++){
								if (i) liftedMethod.name += ",";
								liftedMethod.name += domain.constants[unitGroundedMethod.arguments[i]];
							}
							liftedMethod.name += "]";
	
							// if the method we have to apply is empty
							if (unitGroundedMethod.groundedPreconditions.size() == 0){
								emptyExpanded = true;
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
								break; // we can't go on from here, we have to restart the loop. It is too dangerous
							} else {
							
								// set first subtask and add the rest
								groundedMethod.groundedPreconditions[subTaskIdx] = unitGroundedMethod.groundedPreconditions[0];
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
	
	
								// update table accordingly as new tasks are now contained in this method 
								for (size_t i = 0; i < unitGroundedMethod.groundedPreconditions.size(); i++){
									taskToMethodsTheyAreContainedIn[unitGroundedMethod.groundedPreconditions[i]].insert(groundedMethod.groundedNo);
								}
							}
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



void doBoth (const Domain & domain, const Problem & problem, bool enableHierarchyTyping, bool outputForPlanner)
{
	std::unique_ptr<HierarchyTyping> hierarchyTyping;
	if (enableHierarchyTyping)
		hierarchyTyping = std::make_unique<HierarchyTyping> (domain, problem);

	std::cerr << "Running PG." << std::endl;
	GpgPlanningGraph pg (domain, problem);
	std::vector<GpgPlanningGraph::ResultType> groundedTasksPg;
	std::set<GpgPlanningGraph::StateType> reachableFacts;
	runGpg (pg, groundedTasksPg, reachableFacts, hierarchyTyping.get ());
	assignGroundNosToDeleteEffects(domain, groundedTasksPg, reachableFacts);

	validateGroundedList (groundedTasksPg);

	std::cerr << "PG done." << std::endl;
	std::cerr << "Calculated [" << groundedTasksPg.size () << "] grounded tasks and [" << reachableFacts.size () << "] reachable facts." << std::endl;

#ifdef PRINT_DEBUG_STUFF
	std::cerr << "After lifted PG:" << std::endl;
	for (size_t taskIdx = 0; taskIdx < groundedTasksPg.size (); ++taskIdx)
	{
		const GroundedTask & task = groundedTasksPg[taskIdx];
		assert (task.taskNo < domain.nPrimitiveTasks);
		assert (task.groundedPreconditions.size () == domain.tasks[task.taskNo].preconditions.size ());
		assert (task.groundedDecompositionMethods.size () == 0);
		std::cerr << "    Task " << taskIdx << " (" << task.groundedNo << ", " << ((task.taskNo < domain.nPrimitiveTasks) ? "primitive" : " abstract") << "): " << task.groundedPreconditions.size () << " grounded preconditions (vs " << domain.tasks[task.taskNo].preconditions.size () << "), "
			<< task.groundedDecompositionMethods.size () << " grounded decomposition methods (vs " << domain.tasks[task.taskNo].decompositionMethods.size () << ")." << std::endl;
	}
#endif

	DEBUG (
	for (const auto & fact : reachableFacts)
	{
		std::cerr << "Grounded fact #" << fact.groundedNo << " (" << domain.predicates[fact.predicateNo].name << ")" << std::endl;
		std::cerr << std::endl;
	}
	);

#if 0
	std::vector<int> groundedTasksByTask (domain.nTotalTasks);
	for (const GroundedTask & task : groundedTasksPg)
		++groundedTasksByTask[task.taskNo];

	for (const auto & _method : domain.decompositionMethods)
	{
		DecompositionMethod & method = const_cast<DecompositionMethod &> (_method);
		std::vector<std::pair<size_t, int>> subtasksWithFrequency;
		for (size_t subtaskIdx = 0; subtaskIdx < method.subtasks.size (); ++subtaskIdx)
		{
			const TaskWithArguments & subtask = method.subtasks[subtaskIdx];
			subtasksWithFrequency.push_back (std::make_pair (groundedTasksByTask[subtask.taskNo], subtaskIdx));
		}
		std::sort (subtasksWithFrequency.begin (), subtasksWithFrequency.end (), std::greater<std::pair<size_t, int>> ());
		std::vector<TaskWithArguments> subtasks (method.subtasks.size ());
		for (size_t subtaskIdx = 0; subtaskIdx < method.subtasks.size (); ++subtaskIdx)
		{
			const auto & foo = subtasksWithFrequency[subtaskIdx];
			subtasks[subtaskIdx] = method.subtasks[foo.second];
		}
		method.subtasks = subtasks;
		// TODO: sort ordering constraints
	}
#endif

#ifndef TDG
	const std::vector<GroundedTask> tasksToPrint = groundedTasksPg;
#else
	std::cerr << "Running TDG." << std::endl;
	GpgTdg tdg (domain, problem, groundedTasksPg);
	std::vector<GpgTdg::ResultType> groundedMethods;
	std::set<GpgTdg::StateType> groundedTaskSetTdg;
	runGpg (tdg, groundedMethods, groundedTaskSetTdg, hierarchyTyping.get ());
	std::cerr << "TDG done." << std::endl;
	std::cerr << "Calculated [" << groundedTaskSetTdg.size () << "] grounded tasks and [" << groundedMethods.size () << "] grounded decomposition methods." << std::endl;

	validateGroundedList (groundedMethods);

	// Order grounded tasks correctly
	std::vector<GroundedTask> groundedTasksTdg (groundedTaskSetTdg.size ());
	for (const auto & task : groundedTaskSetTdg)
		groundedTasksTdg[task.groundedNo] = task;

	// Add grounded decomposition methods to the abstract tasks
	for (const GroundedMethod & method : groundedMethods)
		for (auto abstractGroundedTaskNo : method.groundedAddEffects)
			groundedTasksTdg[abstractGroundedTaskNo].groundedDecompositionMethods.push_back (method.groundedNo);

	validateGroundedList (groundedTasksTdg);

	DEBUG (
	for (const auto & task : groundedTasksTdg)
	{
		std::cerr << "Grounded task #" << task.groundedNo << " (" << domain.tasks[task.taskNo].name << ")" << std::endl;
		std::cerr << "Grounded decomposition methods:";
		for (const auto & prec : task.groundedDecompositionMethods)
			std::cerr << " " << prec;
		std::cerr << std::endl;
		std::cerr << "Grounded preconditions:";
		for (const auto & prec : task.groundedPreconditions)
			std::cerr << " " << prec;
		std::cerr << std::endl;
		std::cerr << "Grounded add effects:";
		for (const auto & prec : task.groundedAddEffects)
			std::cerr << " " << prec;
		std::cerr << std::endl;
		std::cerr << std::endl;
	}

	for (const auto & method : groundedMethods)
	{
		std::cerr << "Grounded method #" << method.groundedNo << " (" << domain.decompositionMethods[method.methodNo].name << ")" << std::endl;
		std::cerr << "Grounded preconditions:";
		for (const auto & prec : method.groundedPreconditions)
			std::cerr << " " << prec << " (" << domain.tasks[groundedTasksTdg[prec].taskNo].name << ")";
		std::cerr << std::endl;
		std::cerr << "Grounded add effects:";
		for (const auto & prec : method.groundedAddEffects)
			std::cerr << " " << prec << " (" << domain.tasks[groundedTasksTdg[prec].taskNo].name << ")";
		std::cerr << std::endl;
		std::cerr << std::endl;
	}
	);

	// Perform DFS
	std::cerr << "Performing DFS." << std::endl;
	std::vector<GroundedTask> reachableTasksDfs;
	std::vector<GroundedMethod> reachableMethodsDfs;
	tdgDfs (reachableTasksDfs, reachableMethodsDfs, groundedTasksTdg, groundedMethods, domain, problem);
	std::cerr << "DFS done." << std::endl;
	std::cerr << "After DFS: " << reachableTasksDfs.size () << " tasks, " << reachableMethodsDfs.size () << " methods." << std::endl;

#ifdef PRINT_DEBUG_STUFF
	size_t tmp = 0;
	for (const auto & t : reachableTasksDfs)
		if (t.taskNo < domain.nPrimitiveTasks)
			++tmp;
	std::cerr << "Primitive: " << tmp << std::endl;
#endif

#if 0
	// Check for duplicates
	std::set<GroundedTask> foo1 (reachableTasksDfs.begin (), reachableTasksDfs.end ());
	std::set<GroundedMethod> foo2 (reachableMethodsDfs.begin (), reachableMethodsDfs.end ());
	std::cerr << "Without duplicates: " << reachableTasksDfs.size () << " (" << foo1.size () << ") tasks, " << reachableMethodsDfs.size () << " (" << foo2.size () << ") methods" << std::endl;
#endif

	validateGroundedList (reachableTasksDfs);
	validateGroundedList (reachableMethodsDfs);

	std::vector<GroundedTask> resultTasks;
	resultTasks.reserve (reachableTasksDfs.size ());

	std::vector<Fact> resultFacts;
	resultFacts.reserve (reachableFacts.size ());

	// Iterate grounded PG and TDG until convergence
	std::vector<bool> prunedTasks (reachableTasksDfs.size ());
	std::vector<bool> prunedFacts (reachableFacts.size ());
	std::vector<bool> prunedMethods (reachableMethodsDfs.size ());

	std::vector<GroundedTask> inputTasksGroundedPg = reachableTasksDfs;
	std::vector<Fact> inputFactsGroundedPg (reachableFacts.size ());
	for (const Fact & fact : reachableFacts)
		inputFactsGroundedPg[fact.groundedNo] = fact;
	validateGroundedList (inputFactsGroundedPg);
	std::vector<GroundedMethod> inputMethodsGroundedTdg = reachableMethodsDfs;

	size_t remainingFactsCount = inputFactsGroundedPg.size ();
	size_t remainingMethodsCount = inputMethodsGroundedTdg.size ();

	size_t remainingPrimitiveTasks = 0;
	for (const auto & task : reachableTasksDfs)
	{
		if (task.taskNo < domain.nPrimitiveTasks)
			++remainingPrimitiveTasks;
	}

	while (true)
	{
		// Grounded PG
		std::vector<bool> factReached;
		std::vector<int> unfulfilledPreconditions;
		auto [reachedTasksCount, reachedFactsCount] = groundedPg (factReached, unfulfilledPreconditions, prunedTasks, prunedFacts, inputTasksGroundedPg, inputFactsGroundedPg, domain, problem);

		std::cerr << "Grounded PG:" << std::endl;
		std::cerr << "Input was [" << remainingPrimitiveTasks << ", " << remainingFactsCount << "], output was [" << reachedTasksCount << ", " << reachedFactsCount << "]." << std::endl;
#ifdef PRINT_DEBUG_STUFF
		for (size_t taskIdx = 0; taskIdx < inputTasksGroundedPg.size (); ++taskIdx)
		{
			const GroundedTask & task = inputTasksGroundedPg[taskIdx];
			assert (task.groundedNo == taskIdx);
			std::cerr << "    Task " << taskIdx << " (" << task.groundedNo << ", " << ((task.taskNo < domain.nPrimitiveTasks) ? "primitive" : " abstract") << "): " << unfulfilledPreconditions[task.groundedNo] << " unfulfilled preconditions." << std::endl;
		}
#endif

		remainingFactsCount = reachedFactsCount;

		if (reachedTasksCount == remainingPrimitiveTasks)
			break;

		remainingPrimitiveTasks = reachedTasksCount;

		// Do grounded TDG
		std::vector<bool> taskReached;
		//std::vector<int> unfulfilledPreconditions;
		auto [reachedMethodsCount, reachedTasksCountTdg] = groundedTdg (taskReached, unfulfilledPreconditions, prunedMethods, prunedTasks, inputMethodsGroundedTdg, inputTasksGroundedPg, domain, problem);
		std::cerr << "Grounded TDG:" << std::endl;
		std::cerr << "Input was [" << remainingMethodsCount << ", " << remainingPrimitiveTasks << "], output was [" << reachedMethodsCount << ", " << reachedTasksCountTdg << "]." << std::endl;

		// Do DFS
		auto [reachedPrimitiveTasksCountDfs, reachedMethodsCountDfs] = groundedTdgDfs (prunedTasks, prunedMethods, inputTasksGroundedPg, inputMethodsGroundedTdg, domain, problem);

		// set this early
		remainingMethodsCount = reachedMethodsCountDfs;
		
		if (reachedPrimitiveTasksCountDfs == remainingPrimitiveTasks)
			break;

		remainingPrimitiveTasks = reachedPrimitiveTasksCountDfs;
	}

	// FIXME
	resultTasks = inputTasksGroundedPg;

	std::cerr << "Copying tasks." << std::endl;
	std::vector<GroundedTask> tasksToPrint;
#if 0
	std::copy_if (resultTasks.begin (), resultTasks.end (), std::back_inserter (tasksToPrint), [& domain](const GroundedTask & task) { return task.taskNo < domain.nPrimitiveTasks; });
#else
	std::copy_if (resultTasks.begin (), resultTasks.end (), std::back_inserter (tasksToPrint), [& domain, & prunedTasks](const GroundedTask & task) { return task.taskNo < domain.nPrimitiveTasks && !prunedTasks[task.groundedNo]; });
#endif

	std::vector<GroundedMethod> methodsToPrint;
	//std::copy_if (reachableMethodsDfs.begin (), reachableMethodsDfs.end (), std::back_inserter (methodsToPrint), [& domain, & problem](const GroundedMethod & method) { return domain.decompositionMethods[method.methodNo].taskNo != problem.initialAbstractTask; });
	std::copy_if (inputMethodsGroundedTdg.begin (), inputMethodsGroundedTdg.end (), std::back_inserter (methodsToPrint), [& domain, & problem, & prunedMethods](const GroundedMethod & method) { return domain.decompositionMethods[method.methodNo].taskNo != problem.initialAbstractTask && !prunedMethods[method.groundedNo]; });
	std::cerr << "Done." << std::endl;

	//resultFacts; clear?
	std::copy_if (inputFactsGroundedPg.begin (), inputFactsGroundedPg.end (), std::back_inserter (resultFacts), [& prunedFacts](const Fact & fact) { return !prunedFacts[fact.groundedNo]; });

#endif
	//TODO: FLAGS!!!

	removeUnnecessaryFacts(domain, prunedTasks, prunedFacts, inputTasksGroundedPg, inputFactsGroundedPg);
	expandAbstractTasksWithSingleMethod(domain, problem, prunedTasks, prunedMethods, inputTasksGroundedPg, inputMethodsGroundedTdg);
	

	int absTask = 0;
	int primTask = 0;
	int methods = 0;
	for(int i = 0; i < resultTasks.size(); i++)
		if (! prunedTasks[i]){
			if (resultTasks[i].taskNo >= domain.nPrimitiveTasks)
				absTask++;
			else
				primTask++;
		}
	for (auto & method : inputMethodsGroundedTdg){
		if (prunedMethods[method.groundedNo]) continue;
		methods++;
	}

	// generate output for the planner if necessary
	if (outputForPlanner){
		int evalFact = 0;
		int evalPrimitive = 0;
		int evalMethodPrec = 0;
		int evalAbstract = 0;
		int evalMethod = 0;


		std::cout << ";; #state features" << std::endl;
		std::cout << remainingFactsCount << std::endl;
		int fn = 0;
		for (Fact & fact : inputFactsGroundedPg){
			if (prunedFacts[fact.groundedNo]) continue;
			fact.outputNo = fn++; // assign actual index to fact
			std::cout << domain.predicates[fact.predicateNo].name << "[";
			for (unsigned int i = 0; i < fact.arguments.size(); i++){
				if (i) std::cout << ",";
				std::cout << domain.constants[fact.arguments[i]];
			}
			std::cout << "]" << std::endl;
		}
		assert(fn == remainingFactsCount);
		evalFact = fn;
		std::cout << std::endl;


		// as long as we can't output true SAS+, we simply output the fact list again
		std::cout << ";; Mutex Groups" << std::endl;
		std::cout << remainingFactsCount << std::endl;
		for (Fact & fact : inputFactsGroundedPg){
			if (prunedFacts[fact.groundedNo]) continue;
			std::cout << fact.outputNo << " " << fact.outputNo << " ";
			std::cout << domain.predicates[fact.predicateNo].name << "[";
			for (unsigned int i = 0; i < fact.arguments.size(); i++){
				if (i) std::cout << ",";
				std::cout << domain.constants[fact.arguments[i]];
			}
			std::cout << "]" << std::endl;
		}
		std::cout << std::endl;


		std::cout << ";; Actions" << std::endl;
		std::cout << primTask << std::endl; 
		int ac = 0;
		for (GroundedTask & task : reachableTasksDfs){
			if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;

			task.outputNo = ac++;
			// TODO: for now all actions have cost 1
			std::cout << 1 << std::endl;
			for (int & prec : task.groundedPreconditions)
				std::cout << inputFactsGroundedPg[prec].outputNo << " ";
			std::cout << -1 << std::endl;
			
			for (int & add : task.groundedAddEffects)
				std::cout << inputFactsGroundedPg[add].outputNo << " ";
			std::cout << -1 << std::endl;
			
			for (int & del : task.groundedDelEffects)
				std::cout << inputFactsGroundedPg[del].outputNo << " ";
			std::cout << -1 << std::endl;
		}

		std::cout << std::endl << ";; initial state" << std::endl;
		for (const Fact & f : problem.init){
			std::cout << inputFactsGroundedPg[reachableFacts.find(f)->groundedNo].outputNo << " ";
		}
		std::cout << -1 << std::endl;
		std::cout << std::endl << ";; goal" << std::endl;
		for (const Fact & f : problem.goal){
			auto it = reachableFacts.find(f);
			if (it == reachableFacts.end()){
				// TODO detect this earlier and do something intelligent
				std::cerr << "Goal is unreachable ..." << std::endl;
				_exit(0);
			}
			std::cout << inputFactsGroundedPg[it->groundedNo].outputNo << " ";
		}
		std::cout << -1 << std::endl;

		
		std::cout << std::endl << ";; tasks (primitive and abstract)" << std::endl;
		std::cout << ac + absTask << std::endl;
		// count number of reachable  abstracts
		for (GroundedTask & task : reachableTasksDfs){
			if (prunedTasks[task.groundedNo]) continue;
			if (task.taskNo >= domain.nPrimitiveTasks) continue;
			std::cout << 0 << " ";
			
			if (domain.tasks[task.taskNo].name.rfind("method_precondition_",0) == 0)
				evalMethodPrec++;
			else
				evalPrimitive++;

			
			std::cout << domain.tasks[task.taskNo].name << "[";
			for (unsigned int i = 0; i < task.arguments.size(); i++){
				if (i) std::cout << ",";
				std::cout << domain.constants[task.arguments[i]];
			}
			std::cout << "]" << std::endl;
		}

		int initialAbstract = -1;
		for (GroundedTask & task : reachableTasksDfs){
			if (prunedTasks[task.groundedNo]) continue;
			if (task.taskNo < domain.nPrimitiveTasks) continue;
			task.outputNo = ac++;
			if (task.taskNo == problem.initialAbstractTask) initialAbstract = task.outputNo; 

			std::cout << 1 << " ";

			evalAbstract++;

			std::cout << domain.tasks[task.taskNo].name << "[";
			for (unsigned int i = 0; i < task.arguments.size(); i++){
				if (i) std::cout << ",";
				std::cout << domain.constants[task.arguments[i]];
			}
			std::cout << "]" << std::endl;
		}


		std::cout << std::endl << ";; initial abstract task" << std::endl;
		std::cout << initialAbstract << std::endl;


		std::cout << std::endl << ";; methods" << std::endl;
		std::cout << methods << std::endl;
		int mc = 0;
		for (auto & method : inputMethodsGroundedTdg){
			if (prunedMethods[method.groundedNo]) continue;
			mc++;
			// output their name
			std::cout << domain.decompositionMethods[method.methodNo].name << "[";
			for (unsigned int i = 0; i < method.arguments.size(); i++){
				if (i) std::cout << ",";
				std::cout << domain.constants[method.arguments[i]];
			}
			std::cout << "]" << std::endl;

			// the abstract tasks
			std::cout << reachableTasksDfs[method.groundedAddEffects[0]].outputNo << std::endl;
			for (int & subtask : method.groundedPreconditions){
				std::cout << reachableTasksDfs[subtask].outputNo << " ";
			}
			std::cout << "-1" << std::endl;

			for (auto & order : domain.decompositionMethods[method.methodNo].orderingConstraints)
				std::cout << order.first << " " << order.second << " ";
			std::cout << "-1" << std::endl;
		}
		evalMethod = mc;


		// exiting this way is faster as data structures will not be cleared ... who needs this anyway
		std::cerr << "Exiting." << std::endl;
		std::cerr << "Statistics: " << evalFact << " " << evalPrimitive << " " << evalMethodPrec << " " << evalAbstract << " " << evalMethod << std::endl;
		_exit (0);
	}




	// Output
#if defined(TDG) and defined(PRINT_METHODS)
# if 1
	std::cout << "Size " << tasksToPrint.size () << " " << absTask << " " << methodsToPrint.size () << std::endl;
	std::cerr << remainingPrimitiveTasks << " " << remainingFactsCount << " " << remainingMethodsCount << std::endl;
	assert (tasksToPrint.size () == remainingPrimitiveTasks);
	assert (resultFacts.size () == remainingFactsCount);
	//assert (methodsToPrint.size () == remainingMethodsCount - 1);
# else
	std::cout << "Size " << tasksToPrint.size () << " " << resultFacts.size () << " " << methodsToPrint.size () << std::endl;
# endif
#else
	std::vector<Fact> resultFacts (reachableFacts.begin (), reachableFacts.end ());
	std::cout << tasksToPrint.size () << " " << resultFacts.size () << std::endl;
#endif

	//return;

	// Helper vector for sorting the output
	std::vector<std::string> sortVec;

	// First print all grounded tasks
	sortVec.clear ();
	for (const GroundedTask & groundedTask : tasksToPrint)
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
	for (const Fact & fact : resultFacts)
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

#if defined(TDG) and defined(PRINT_METHODS)
	// Then print all grounded methods
	sortVec.clear ();
	for (const GroundedMethod & method : methodsToPrint)
	{
		const DecompositionMethod & liftedMethod = domain.decompositionMethods[method.methodNo];

		std::stringstream stream;
		stream << liftedMethod.name;
		for (int argument : method.arguments)
			stream << " " << domain.constants[argument];

		sortVec.push_back (stream.str ());
	}

	sort (sortVec.begin (), sortVec.end ());
	for (const std::string & str : sortVec)
		std::cout << str << std::endl;
#endif
}

/**
 * @}
 */

#endif
