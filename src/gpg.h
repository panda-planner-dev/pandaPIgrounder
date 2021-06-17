#ifndef GPG_H_INCLUDED
#define GPG_H_INCLUDED

/**
 * @defgroup gpg Generalized Planning Graph
 *
 * @{
 */

#include <ctime>

#include <algorithm>
#include <functional>
#include <iomanip>
#include <iostream>
#include <memory>
#include <numeric>
#include <queue>
#include <set>
#include <sstream>
#include <vector>
#include <ostream>
#include <map>
#include <cassert>
#include <unistd.h>
#include <unordered_set>


#include "debug.h"
#include "hierarchy-typing.h"
#include "model.h"
#include "rss.h"

#define TDG
#define PRINT_METHODS

using namespace pandaPI;

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

	//requires bool pruneWithHierarchyTyping;
	//requires bool pruneWithFutureSatisfiablility;
	// ...other things?
};

template <Literal T>
struct GpgLiteralSet
{
	/// Contains a std::set<T> for each predicate.
	std::vector<std::unordered_set<T>> factsByPredicate;

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
	const T* insert (const T & fact)
	{
		assert (fact.getHeadNo () < factsByPredicate.size ());

		return &(*(factsByPredicate[fact.getHeadNo ()].insert (fact).first));
	}

	/**
	 * @brief Returns the set of facts for the given predicate.
	 *
	 * It is an error to call this function with a predicateNo which is greater than or equal to nPredicates as passed to the constructor of this GpgLiteralSet.
	 */
	const std::unordered_set<T> & getFactsForPredicate (int headNo) const
	{
		assert (headNo < factsByPredicate.size ());

		return factsByPredicate[headNo];
	}

	/**
	 * @brief Returns an iterator to the given fact in the set.
	 *
	 * If the given fact is not in the set, the returned iterator is equal to end(fact.getHeadNo()).
	 */
	typename std::unordered_set<T>::const_iterator find (const T & fact) const
	{
		return factsByPredicate[fact.getHeadNo ()].find (fact);
	}

	/**
	 * @brief Returns the end iterator for the fact set for the given predicate.
	 */
	typename std::unordered_set<T>::const_iterator end (int headNo) const
	{
		return factsByPredicate[headNo].end ();
	}

	/// Returns a std::set containing all facts in this GpgLiteralSet.
	operator std::set<T> (void) 
	{
		std::set<T> result;
		for (size_t i = 0; i < factsByPredicate.size(); i++){
			// remove elements from factsByPredicate while iterating ... this is more memory efficient
			auto it = factsByPredicate[i].begin();
			while (it != factsByPredicate[i].end()){
				result.insert(*it);
				it = factsByPredicate[i].erase(it);
			}
		}
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
	std::vector<std::vector<std::map<int, int>>> assignedVariablesByTaskAndPrecondition;
	std::vector<std::vector<std::vector<std::set<int>>>> assignedVariablesSet;

	/**
	 * @brief For every task and precondition, a list of sets (saved as vector) argument numbers that must be identical (due to the fact that they are instantiated with the same variable)
	 */
	std::vector<std::vector<std::vector<std::vector<int>>>> identicalArgumentsByTaskAndPrecondition;

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


	bool hasVariable(int actionIdx, int preconditionIdx, int initiallyMatchedPrecondition, int var)	const {
		auto it = assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx].find(initiallyMatchedPrecondition);
		if (it == assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx].end()) return false;

		return assignedVariablesSet[actionIdx][preconditionIdx][it->second].count(var) > 0;
	}

	/**
	 * @brief Preprocesses the given Domain.
	 *
	 * If enableHierarchyTyping is given, the Hierarchy Typing will be calculated using the given Domain and Problem,
	 * and can then be used by the Planning Graph.
	 */
	GpgPreprocessedDomain (const InstanceType & instance, const Domain & domain, const Problem & problem) : domain (domain)
	{
		assignedVariablesByTaskAndPrecondition.resize (instance.getNumberOfActions ());
		assignedVariablesSet.resize (instance.getNumberOfActions ());
		identicalArgumentsByTaskAndPrecondition.resize (instance.getNumberOfActions ());
		preconditionsByPredicate.resize (instance.getNumberOfPredicates ());
		eligibleInitialPreconditionsByAction.resize (instance.getNumberOfActions ());

		for (size_t actionIdx = 0; actionIdx < instance.getNumberOfActions (); ++actionIdx)
		{
			const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];

			assignedVariablesByTaskAndPrecondition[actionIdx].resize (action.getAntecedents ().size ());
			assignedVariablesSet[actionIdx].resize (action.getAntecedents ().size ());
			identicalArgumentsByTaskAndPrecondition[actionIdx].resize (action.getAntecedents ().size ());

			for (size_t preconditionIdx = 0; preconditionIdx < action.getAntecedents ().size (); ++preconditionIdx){
				const typename InstanceType::PreconditionType & precondition = action.getAntecedents ()[preconditionIdx];
				std::map<int,std::vector<int>> variablesAt;
				for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
				{
					int variable = precondition.arguments[argumentIdx];
					variablesAt[variable].push_back(argumentIdx);
				}

				for (auto & entry : variablesAt) if (entry.second.size() > 1){
					identicalArgumentsByTaskAndPrecondition[actionIdx][preconditionIdx].push_back(entry.second);
				}
			}

			// Determine which preconditions are eligible for optimization
			for (size_t preconditionIdx = 0; preconditionIdx < action.getAntecedents ().size (); ++preconditionIdx){
				const typename InstanceType::PreconditionType & precondition = action.getAntecedents ()[preconditionIdx];
				bool allVariablesAreConstants = true;
				for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
				{
					int variable = precondition.arguments[argumentIdx];
					allVariablesAreConstants &= domain.sorts[action.variableSorts[variable]].members.size() == 1;
				}

				if (allVariablesAreConstants) continue;

				eligibleInitialPreconditionsByAction[actionIdx].insert (preconditionIdx);
			}

			std::set<int> alreadyAssignedVariables;
			for (size_t preconditionIdx = 0; preconditionIdx < action.getAntecedents ().size (); ++preconditionIdx)
			{
				std::map<std::set<int>,int> assignedVariablesToID;
				// Calculate which variables are assigned when a precondition is matched
				
				auto variableAssignmentIterator = assignedVariablesToID.find(alreadyAssignedVariables);
				int assignmentID = -1;
				if (variableAssignmentIterator == assignedVariablesToID.end()){
					assignmentID = assignedVariablesToID.size();
					assignedVariablesToID[alreadyAssignedVariables] = assignmentID;
					assignedVariablesSet[actionIdx][preconditionIdx].push_back(alreadyAssignedVariables);
				} else {
					assignmentID = variableAssignmentIterator->second;
				}

				assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx][-1] = assignmentID;
				
				
				for (size_t initiallyMatchedPreconditionIdx : eligibleInitialPreconditionsByAction[actionIdx])
				{
					std::set<int> innerAssignedVariables = alreadyAssignedVariables;

					const typename InstanceType::PreconditionType & initiallyMatchedPrecondition = action.getAntecedents ()[initiallyMatchedPreconditionIdx];
					for (size_t argumentIdx = 0; argumentIdx < initiallyMatchedPrecondition.arguments.size (); ++argumentIdx)
					{
						int variable = initiallyMatchedPrecondition.arguments[argumentIdx];
						innerAssignedVariables.insert (variable);
					}

					variableAssignmentIterator = assignedVariablesToID.find(innerAssignedVariables);
					assignmentID = -1;
					if (variableAssignmentIterator == assignedVariablesToID.end()){
						assignmentID = assignedVariablesToID.size();
						assignedVariablesToID[innerAssignedVariables] = assignmentID;
						assignedVariablesSet[actionIdx][preconditionIdx].push_back(innerAssignedVariables);
					} else {
						assignmentID = variableAssignmentIterator->second;
					}

					assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx][initiallyMatchedPreconditionIdx] = assignmentID;
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


	// temp
	DEBUG(
		for (size_t actionIdx = 0; actionIdx < instance.getNumberOfActions (); ++actionIdx){
			const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];
			int ante = action.getAntecedents ().size();	
			std::cout << "Action " << actionIdx << " " << instance.getAllActions()[actionIdx].name << std::endl;
			if (action.getAntecedents().size() > 20) continue;
			for (size_t preconditionIdx = 0; preconditionIdx < action.getAntecedents ().size (); ++preconditionIdx){
				std::cout << "  Prec " << preconditionIdx << " " << assignedVariablesSet[actionIdx][preconditionIdx].size() << " of " << (ante+1) << std::endl;	
				for (auto s : assignedVariablesSet[actionIdx][preconditionIdx]){
					std::cout << "    ";
					bool first = true;
					for (int x : s){
						if (!first) std::cout << " ";
						std::cout << x;
						first = false;
					}
					std::cout << std::endl;	
				}
			
			}
		}
	);



	}
};


namespace std {
    template<> struct hash<std::vector<int>>
    {
        std::size_t operator()(const std::vector<int>& v) const noexcept
        {
			std::size_t h = 0;
			for (const int & a : v) h = h*601 + a;

			return h;
        }
    };
}


/**
 * @brief Allows efficient access to Facts that could potentially satisfy a precondition.
 */
template <GpgInstance InstanceType>
struct GpgStateMap
{
	using VariablesToFactListMap = std::map<std::vector<int>, std::vector<int>>;

	/**
	 * @brief The GPG instance.
	 */
	const InstanceType & instance;

	/**
	 * @brief The preprocessed domain.
	 */
	const GpgPreprocessedDomain<InstanceType> & preprocessedDomain;

	/**
	 * @brief if true, future consistency will be cached separately per initially matched precondition
	 */
	bool futureCachingByPrecondition;

	/**
	 * save state elements in extra list
	 */
	std::vector<const typename InstanceType::StateType*> addedStateElements;

	/**
	 * @brief A list of Facts for each task, precondition, and ID of assigned variables and actually assigned constants.
	 */
	std::vector<std::vector<std::vector<VariablesToFactListMap>>> factMap;


	std::vector<int> numberOfAntecedantsWithoutFact;

	/**
	 * @brief Whether a fact exists for each task, precondition, future precondition and initially matched precondition (-1 if not eligible) and set of assigned variables.
	 * note that the index of the precondition is moved by one, i.e. 0 represents precondition -1 (i.e. none matched so far) and size-1 is actually size-2 as it is not necessary to check for the last precondition at all
	 */
	std::vector<std::vector<std::vector<std::map<int, std::unordered_set<std::vector<int>>>>>> consistency;
	
	/**
	 * @brief Initializes the factMap.
	 */
	GpgStateMap (const InstanceType & instance, const GpgPreprocessedDomain<InstanceType> & preprocessedDomain, bool _futureCachingByPrecondition) : 
		instance (instance), preprocessedDomain (preprocessedDomain), futureCachingByPrecondition(_futureCachingByPrecondition)
	{
		numberOfAntecedantsWithoutFact.resize(instance.getNumberOfActions());
		factMap.resize (instance.getNumberOfActions ());
		consistency.resize (instance.getNumberOfActions ());

		for (size_t actionIdx = 0; actionIdx < instance.getNumberOfActions (); ++actionIdx)
		{
			const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];
			factMap[actionIdx].resize (action.getAntecedents ().size ());
			consistency[actionIdx].resize (action.getAntecedents().size () + 1);
			numberOfAntecedantsWithoutFact[actionIdx] = action.getAntecedents().size();
			
			for (size_t preconditionIdx = 0; preconditionIdx < action.getAntecedents().size()+1; preconditionIdx++)
				consistency[actionIdx][preconditionIdx].resize (action.getAntecedents ().size ());
			
			for (size_t preconditionIdx = 0; preconditionIdx < action.getAntecedents().size(); preconditionIdx++)
				factMap[actionIdx][preconditionIdx].resize(preprocessedDomain.assignedVariablesSet[actionIdx][preconditionIdx].size());
		}
	}

	/**
	 * @brief Inserts a Fact into the maps of all preconditions with the same predicate as the Fact.
	 */
	void insertState (const typename InstanceType::StateType * stateElement)
	{
		int stateElementIndex = addedStateElements.size();
		addedStateElements.push_back(stateElement);
		
		for (const auto & [actionIdx, preconditionIdx] : preprocessedDomain.preconditionsByPredicate[stateElement->getHeadNo ()])
		{
			const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];
			const typename InstanceType::PreconditionType & precondition = action.getAntecedents ()[preconditionIdx];

			assert (precondition.arguments.size () == stateElement->arguments.size ());

			std::vector<int> values;

			for (const std::vector<int> & identical_group : preprocessedDomain.identicalArgumentsByTaskAndPrecondition[actionIdx][preconditionIdx]){
				int val = stateElement->arguments[identical_group[0]];
				for (size_t i = 1; i < identical_group.size(); i++)
					if (stateElement->arguments[identical_group[i]] != val)
						goto next_action;
			}

			// Ineligible initially matched precondition
			for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
			{
				int var = precondition.arguments[argumentIdx];

				// Skip this fact if its variables are incompatible with the sorts defined by the action
				int value = stateElement->arguments[argumentIdx];
				if (preprocessedDomain.domain.sorts[action.variableSorts[var]].members.count (value) == 0)
					goto next_action;

				if (preprocessedDomain.hasVariable(actionIdx,preconditionIdx,-1,var))
					values.push_back (value);
			}
			if (factMap[actionIdx][preconditionIdx][0].size() == 0) // works as the assignment without a matched precondition is always the first
				numberOfAntecedantsWithoutFact[actionIdx]--;


			for (size_t variablesNumber = 0; variablesNumber < preprocessedDomain.assignedVariablesSet[actionIdx][preconditionIdx].size(); variablesNumber++){
				const std::set<int> & assignedVariables = preprocessedDomain.assignedVariablesSet[actionIdx][preconditionIdx][variablesNumber];
				std::vector<int> values;
				for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
				{
					int var = precondition.arguments[argumentIdx];
					int value = stateElement->arguments[argumentIdx];
					// we have already checked this value in the previous loop	

					if (assignedVariables.count(var)) values.push_back(value);
				}
				
				factMap[actionIdx][preconditionIdx][variablesNumber][values].push_back(stateElementIndex);
			}

			if (! instance.pruneWithFutureSatisfiablility[actionIdx]) continue;
			
			// mark as potential future precondition
			for (int pastPreconditionIdx = -1; pastPreconditionIdx < preconditionIdx; pastPreconditionIdx++){
				
				// Ineligible initially matched precondition
				std::vector<int> values;
				for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
				{
					int var = precondition.arguments[argumentIdx];
	
					// check whether this variable will already have been set by the past precondition
					if (preprocessedDomain.hasVariable(actionIdx,pastPreconditionIdx+1,-1,var))
					{
						values.push_back (stateElement->arguments[argumentIdx]);
					}
				}
				consistency[actionIdx][pastPreconditionIdx+1][preconditionIdx][-1].insert(values);

				if (!futureCachingByPrecondition) continue;	
				// Eligible initially matched preconditions
				for (int initiallyMatchedPreconditionIdx : preprocessedDomain.eligibleInitialPreconditionsByAction[actionIdx])
				{
					std::vector<int> values;
					for (size_t argumentIdx = 0; argumentIdx < precondition.arguments.size (); ++argumentIdx)
					{
						int var = precondition.arguments[argumentIdx];
						if (preprocessedDomain.hasVariable(actionIdx,pastPreconditionIdx+1,initiallyMatchedPreconditionIdx,var))
						{
							values.push_back (stateElement->arguments[argumentIdx]);
						}
					}
	
					consistency[actionIdx][pastPreconditionIdx+1][preconditionIdx][initiallyMatchedPreconditionIdx].insert(values);
				}
			}

next_action:;
		}
	}

	void dropEligibleInitialPrecondition(){
		return;

		std::vector<std::tuple<int,int,int>> eligibleSizes;
		for (size_t a = 0; a < factMap.size(); a++){
			for (size_t p = 0; p < factMap[a].size(); p++){
				for (size_t pp = 1; pp < factMap[a][p].size(); pp++){
					if (!preprocessedDomain.eligibleInitialPreconditionsByAction[a].count(pp-1)) continue;

					eligibleSizes.push_back(std::make_tuple(factMap[a][p][pp].size(), a, pp-1));
				}
			}
		}

		std::sort(eligibleSizes.begin(), eligibleSizes.end());
		// prune 10 largest ones
		for (int i = 0; i < 1 && eligibleSizes.size() - i - 1 >= 0; i++){
			int size = std::get<0>(eligibleSizes[eligibleSizes.size() - i - 1]);
			int a = std::get<1>(eligibleSizes[eligibleSizes.size() - i - 1]);
			int pre = std::get<2>(eligibleSizes[eligibleSizes.size() - i - 1]);
			const_cast<GpgPreprocessedDomain<InstanceType> &>(preprocessedDomain).eligibleInitialPreconditionsByAction[a].erase(pre);
			
			for (size_t p = 0; p < factMap[a].size(); p++)
				factMap[a][p][1+pre].clear();
		}
	}

	/**
	 * @brief Returns all Facts for the given precondition in the given task that are compatible with the given variable assignment.
	 *
	 * For performance reasons, we want to return the Fact vector by reference. This means that we may have to instantiate a new
	 * Fact vector if there is none for the given variable assignment. As a result, this method cannot be declared to be const.
	 */
	std::vector<typename InstanceType::StateType> getFacts (size_t actionIdx, size_t preconditionIdx, const VariableAssignment & assignedVariables, int initiallyMatchedPreconditionIdx)
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
			if (!(preprocessedDomain.hasVariable(actionIdx,preconditionIdx,initiallyMatchedPreconditionIdx,var)))
				continue;

			assert (assignedVariables.isAssigned (var));
			assignedVariableValues.push_back (assignedVariables[var]);
		}

		
		// generate return set
		std::vector<typename InstanceType::StateType> ret;
		int variableID = preprocessedDomain.assignedVariablesByTaskAndPrecondition[actionIdx][preconditionIdx].at(initiallyMatchedPreconditionIdx);
		
		for (int & x : factMap[actionIdx][preconditionIdx][variableID][assignedVariableValues])
			ret.push_back(*addedStateElements[x]);


		return ret;
	}

	bool hasInstanceForAllAntecedants(size_t actionIdx, int initiallyMatchedPreconditionIdx){
		if (numberOfAntecedantsWithoutFact[actionIdx] == 0) return true;
		if (numberOfAntecedantsWithoutFact[actionIdx] >= 2) return false;

		return factMap[actionIdx][initiallyMatchedPreconditionIdx][0].size() == 0;
	}



	// precondition index may be -1 indicating that no precondition has been set yet, except for the initially matched one	
	bool hasPotentiallyConsistentExtension (size_t actionIdx, size_t preconditionIdx, const VariableAssignment & assignedVariables, int initiallyMatchedPreconditionIdx){
		// for testing: always disregard the initially matched Precondition

		bool initiallyMatchedPreconditionIsEligible = preprocessedDomain.eligibleInitialPreconditionsByAction[actionIdx].count (initiallyMatchedPreconditionIdx) > 0;
		if (!initiallyMatchedPreconditionIsEligible || !futureCachingByPrecondition)
			initiallyMatchedPreconditionIdx = -1;
	
		const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];

		// check all future preconditions
		for (size_t futurePreconditionIdx = preconditionIdx + 1; futurePreconditionIdx < action.getAntecedents().size(); futurePreconditionIdx++){
			
			// variables assigned so far that are part of the arguments of the future precondition

			const typename InstanceType::PreconditionType & futurePrecondition = instance.getAllActions()[actionIdx].getAntecedents()[futurePreconditionIdx];
			// Build the vector which is used as the key in the map
			std::vector<int> assignedVariableValues;
			//std::cout << "Action " << action.name << " Current Precondition: " << preconditionIdx << " initial: " << initiallyMatchedPreconditionIdx << " Future Precondition " << instance.getAntecedantName(futurePrecondition.getHeadNo()) << "set variables:"; 
			for (size_t argIdx = 0; argIdx < futurePrecondition.arguments.size (); ++argIdx)
			{
				int var = futurePrecondition.arguments[argIdx];
				// check whether the future precondition will have already been assigned
				if (!(preprocessedDomain.hasVariable(actionIdx,preconditionIdx+1,initiallyMatchedPreconditionIdx,var)))
					continue;
	
				assert (assignedVariables.isAssigned (var));
				//std::cout << " " << var;
				assignedVariableValues.push_back (assignedVariables[var]);
			}
			
			if (consistency[actionIdx][preconditionIdx+1][futurePreconditionIdx][initiallyMatchedPreconditionIdx].count(assignedVariableValues) == 0){
				//std::cout << " -> reject " << std::endl;
				return false;
			}
			//std::cout << " -> accept " << std::endl;
		}

		return true;
	}


	void dropConsistencyTable(){
		consistency.clear();
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
	
	bool allFutureSatisfiabilityDisabled = false;
	std::vector<bool> pruneWithHierarchyTyping;
	std::vector<bool> pruneWithFutureSatisfiablility;

	GpgPlanningGraph (const Domain & domain, const Problem & problem) : domain (domain), problem (problem) {
		for (size_t i = 0; i < domain.nPrimitiveTasks; i++){
			pruneWithFutureSatisfiablility.push_back(true);
			pruneWithHierarchyTyping.push_back(true);
		}
	}

	std::vector<StateType>::iterator getInitialStateStart (void) 
	{
		return const_cast<Problem &>(problem).init.begin();
	}

	void getInitialStateNext (std::vector<StateType>::iterator & it) 
	{
		it++;
	}

	const StateType & getInitialStateElement (std::vector<StateType>::iterator & it) 
	{
		return *it;
	}

	bool isInitialStateEnd (std::vector<StateType>::iterator it) const
	{
		return it == problem.init.end();
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

	const std::string getAntecedantName(int antecedantHeadNo) const
	{
		return domain.predicates[antecedantHeadNo].name;
	}

	bool doesStateFulfillPrecondition (const ActionType & task, VariableAssignment * assignedVariables, const StateType & fact, size_t preconditionIdx) const
	{
		return task.doesFactFulfilPrecondition (assignedVariables, domain, fact, preconditionIdx);
	}

	void disableAllFutureSatisfiability(){
		allFutureSatisfiabilityDisabled = true;
		for (int a = 0; a < getNumberOfActions(); a++)
			disablePruneWithFutureSatisfiablility(a);
	}
	
	void disablePruneWithFutureSatisfiablility(size_t actionIdx){
		pruneWithFutureSatisfiablility[actionIdx] = false;
	}

	void disablePruneWithHierarchyTyping(size_t actionIdx){
		pruneWithHierarchyTyping[actionIdx] = false;
	}
};

extern std::map<int,int> liftedGroundingCount;
extern std::map<int,double> stateElementGroundingTime;
extern std::map<int,double> stateElementMPTime;
extern std::map<int,double> stateElementInsertTime;
extern std::map<int,double> liftedGroundingTime;
extern std::map<int,double> instantiationtime;
extern std::map<int,double> instantiationtime2;

template <GpgInstance InstanceType>
static void gpgAssignVariables (
	const InstanceType & instance,
	const HierarchyTyping * hierarchyTyping,
	std::vector<typename InstanceType::ResultType *> & output,
	std::queue<typename std::unordered_set<typename InstanceType::StateType>::const_iterator> & toBeProcessedQueue,
	std::unordered_set<typename InstanceType::StateType> & toBeProcessedSet,
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
		DEBUG (std::cerr << "All vars assigned" << std::endl);
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

		liftedGroundingCount[actionNo]++;

		// Create and return grounded action
		typename InstanceType::ResultType * result = new typename InstanceType::ResultType();
		result->groundedNo = output.size ();
		result->setHeadNo (actionNo);
		result->arguments = assignedVariables;

		// XXX TODO: insert vector as subtasks of result
		// XXX TODO: insert ground preconditions and add effects
		result->groundedPreconditions = matchedPreconditions;
		// Still anything TODO?
		
		DEBUG(
			std::cout << "  Arguments:";
			for (int a : result->arguments) std::cout << " " << a;
			std::cout << std::endl;
			std::cout << "  Preconditions:";
			for (int p : result->groundedPreconditions) std::cout << " " << p;
			std::cout << std::endl;
							);
		
		// Add "add" effects from this action to our known facts
		for (const typename InstanceType::PreconditionType & addEffect : action.getConsequences ())
		{
			
			typename InstanceType::StateType addState;
			addState.setHeadNo (addEffect.getHeadNo ());
			for (int varIdx : addEffect.arguments)
			{
				assert (assignedVariables.isAssigned (varIdx));
				addState.arguments.push_back (assignedVariables[varIdx]);
			}

			//std::clock_t cc_begin = std::clock();
			// Check if we already know this fact
			bool found = false;
			typename std::unordered_set<typename InstanceType::StateType>::const_iterator factIt;
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
			//std::clock_t cc_end = std::clock();
			//double time_elapsed_ms = 1000.0 * (cc_end-cc_begin) / CLOCKS_PER_SEC;
			//instantiationtime2[actionNo] += time_elapsed_ms;

			// If we already processed this fact, don't add it again
			if (!found)
			{
				// New state element; give it a number
				addState.groundedNo = processedStates.size () + toBeProcessedSet.size ();

				DEBUG(std::cout << "New Fact " << addState.groundedNo << ": " << addEffect.getHeadNo();
				for (int varIdx : addEffect.arguments) std::cout << " " << assignedVariables[varIdx];
				std::cout << std::endl;
				);


				auto [it,_] = toBeProcessedSet.insert (addState);
				toBeProcessedQueue.push (it);
			}

			// Add this add effect to the list of add effects of the result we created
			result->groundedAddEffects.push_back (addState.groundedNo);
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

extern size_t totalFactTests;
extern std::vector<std::vector<std::vector<size_t>>> factTests;
extern size_t totalFactHits;
extern std::vector<std::vector<std::vector<size_t>>> factHits;
extern std::vector<std::vector<std::vector<size_t>>> factFutureRejects;
extern std::vector<std::vector<std::vector<size_t>>> noextensionFound;

extern std::vector<size_t> futureReject;
extern std::vector<size_t> futureTests;
extern std::vector<size_t> htReject;
extern std::vector<size_t> htTests;

template<GpgInstance InstanceType>
void printStatistics(const InstanceType & instance){
	//bool outputPerPrec = true;
	std::cerr << "========================================" << std::endl;
	std::cerr << "Total fact misses: " << (totalFactTests - totalFactHits) << " / " << totalFactTests << " = " << std::fixed << std::setprecision (3) << 100.0 * (totalFactTests - totalFactHits) / totalFactTests << " % (" << totalFactHits << " hits)" << std::endl;
	//for (size_t i = 0; i < instance.getNumberOfActions (); ++i)
	//{
	//	//if (i != 2) continue;
	//	const auto & action = instance.getAllActions ()[i];
	//	std::cerr << "Fact misses for action " << i << " (" << action.name << "):" << std::endl;
	//	std::cerr << "Rejects Future: " << futureReject[i] << " HT: " << htReject[i] << std::endl;
	//	int actionTotal = 0;
	//	for (size_t k = 0; k < action.getAntecedents ().size (); ++k)
	//	{
	//		if (outputPerPrec) std::cerr << "  Initially matched: " << k+1 << std::endl;
	//		for (size_t j = 0; j < action.getAntecedents ().size (); ++j)
	//		{
	//			actionTotal += factTests[i][j][k];
	//			if (outputPerPrec) {
	//				std::cerr << "    Precondition " << (j + 1) << " (" << instance.getAntecedantName(action.getAntecedents()[j].getHeadNo());
	//				for (int arg : action.getAntecedents()[j].arguments)
	//						std::cerr << " " << arg;
	//				std::cerr << "): ";
	//			}
	//			if (outputPerPrec) std::cerr << (factTests[i][j][k] - factHits[i][j][k]) << " / " << factTests[i][j][k] << " = " << std::fixed << std::setprecision (3) << 100.0 * (factTests[i][j][k] - factHits[i][j][k]) / factTests[i][j][k] << " % (" << factHits[i][j][k] << " hits)" << " future rejects " << factFutureRejects[i][j][k] << " no extensions " << noextensionFound[i][j][k] << std::endl;
	//		}
	//	}
	//	std::cerr << "total: " << actionTotal << std::endl;
	//}
	std::cerr << "Current Groundings: " << std::endl;
	for (auto g : liftedGroundingCount)
		std::cerr << "  " << instance.getAllActions()[g.first].name << " " << g.second << std::endl;

	double total = 0;
	std::cerr << "Grounding Time: " << std::endl;
	for (auto g : liftedGroundingTime){
		std::cerr << "  " << instance.getAllActions()[g.first].name << " " << g.second << std::endl;
		total += g.second;
	}
	std::cerr << "  total: " << total << std::endl;

	total = 0;
	std::cerr << "Grounding Time: " << std::endl;
	for (auto g : stateElementGroundingTime) {
		std::cerr << "  " << instance.getAntecedantName(g.first) << " " << g.second << std::endl;
		total += g.second;
	}
	std::cerr << "  total: " << total << std::endl;

	total = 0;
	std::cerr << "Match Precondition Time: " << std::endl;
	for (auto g : stateElementMPTime) {
		std::cerr << "  " << instance.getAntecedantName(g.first) << " " << g.second << std::endl;
		total += g.second;
	}
	std::cerr << "  total: " << total << std::endl;

	total = 0;
	std::cerr << "Insert Time: " << std::endl;
	for (auto g : stateElementInsertTime) {
		std::cerr << "  " << instance.getAntecedantName(g.first) << " " << g.second << std::endl;
		total += g.second;
	}
	std::cerr << "  total: " << total << std::endl;

	std::cerr << "Instantiaton Time: " << std::endl;
	for (auto g : instantiationtime)
		std::cerr << "  " << instance.getAllActions()[g.first].name << " " << g.second << std::endl;
	std::cerr << "Instantiaton Time #2: " << std::endl;
	for (auto g : instantiationtime2)
		std::cerr << "  " << instance.getAllActions()[g.first].name << " " << g.second << std::endl;
}

template<GpgInstance InstanceType>
void gpgMatchPrecondition (
	const InstanceType & instance,
	const HierarchyTyping * hierarchyTyping,
	std::vector<typename InstanceType::ResultType *> & output,
	std::queue<typename std::unordered_set<typename InstanceType::StateType>::const_iterator> & toBeProcessedQueue,
	std::unordered_set<typename InstanceType::StateType> & toBeProcessedSet,
	const GpgLiteralSet<typename InstanceType::StateType> & processedStates,
	GpgStateMap<InstanceType> & stateMap,
	size_t actionNo,
	VariableAssignment & assignedVariables,
	size_t initiallyMatchedPrecondition,
	const typename InstanceType::StateType & initiallyMatchedState,
	std::vector<int> & matchedPreconditions,
	size_t preconditionIdx,
	grounding_configuration & config
)
{
	
	if (preconditionIdx == 0){
		if (instance.pruneWithFutureSatisfiablility[actionNo] && !stateMap.hasPotentiallyConsistentExtension(actionNo, -1, assignedVariables, initiallyMatchedPrecondition)){
			factFutureRejects[actionNo][initiallyMatchedPrecondition][initiallyMatchedPrecondition]++;
			futureReject[actionNo]++;
			return;
		}
	
	}
	
	
	const typename InstanceType::ActionType & action = instance.getAllActions ()[actionNo];

	if (preconditionIdx >= action.getAntecedents ().size ())
	{
		// Processed all preconditions. This is a potentially reachable ground instance.
		// Now we only need to assign all unassigned variables.
		
		//std::clock_t cc_begin = std::clock();
		gpgAssignVariables (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStates, actionNo, assignedVariables, matchedPreconditions);
		//std::clock_t cc_end = std::clock();
		//double time_elapsed_ms = 1000.0 * (cc_end-cc_begin) / CLOCKS_PER_SEC;
		//instantiationtime[actionNo] += time_elapsed_ms;

		return;
	}

	// Skip initially matched precondition
	if (preconditionIdx == initiallyMatchedPrecondition)
	{
		// if the initially matched precondition cannot be extended continue
		//if (!stateMap.hasPotentiallyConsistentExtension(actionNo, preconditionIdx, assignedVariables, initiallyMatchedPrecondition))
		//	return
		
		
		gpgMatchPrecondition (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStates, stateMap, actionNo, assignedVariables, initiallyMatchedPrecondition, initiallyMatchedState, matchedPreconditions, preconditionIdx + 1, config);
		return;
	}

	const typename InstanceType::PreconditionType & precondition = action.getAntecedents ()[preconditionIdx];

	bool foundExtension = false;

	// Try to find a fact that fulfills this precondition
	for (const typename InstanceType::StateType & stateElement : stateMap.getFacts (actionNo, preconditionIdx, assignedVariables, initiallyMatchedPrecondition))
	{
		// Necessary for duplicate elimination. If an action has two preconditions to which the initiallyMatchedState can be matched, we would generate some groundings twice.
		// The currently *new* initiallyMatchedState can only be matched to preconditions before the precondition to which it was matched to start this grounding.
		if (preconditionIdx >= initiallyMatchedPrecondition && stateElement == initiallyMatchedState)
			continue;

		++totalFactTests;
		++factTests[actionNo][preconditionIdx][initiallyMatchedPrecondition];

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
					std::cerr << "Sort does not match" << std::endl;
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
			++factHits[actionNo][preconditionIdx][initiallyMatchedPrecondition];
		}

		// do prediction whether the precondition in the future may still have matching instantiations
		if (factMatches && instance.pruneWithFutureSatisfiablility[actionNo]
				&&preconditionIdx !=  action.getAntecedents().size()-1){
			futureTests[actionNo]++;
			if (!stateMap.hasPotentiallyConsistentExtension(actionNo, preconditionIdx, assignedVariables, initiallyMatchedPrecondition)){
				factFutureRejects[actionNo][preconditionIdx][initiallyMatchedPrecondition]++;
				factMatches = false;
				futureReject[actionNo]++;
			}
		}
		
		if (factMatches && instance.pruneWithHierarchyTyping[actionNo] && hierarchyTyping != nullptr ){
			htTests[actionNo]++;
			if (!hierarchyTyping->isAssignmentCompatible<typename InstanceType::ActionType> (actionNo, assignedVariables)){
				factMatches = false;
				htReject[actionNo]++;
			}
		}

		// check variable constraints ahead
		if (factMatches){
			for (const VariableConstraint & constraint : action.variableConstraints)
			{
				if (!assignedVariables.isAssigned (constraint.var1)) continue;
				if (!assignedVariables.isAssigned (constraint.var2)) continue;
				
				int val1 = assignedVariables[constraint.var1];
				int val2 = assignedVariables[constraint.var2];
				if (constraint.type == VariableConstraint::Type::EQUAL)
				{
					if (val1 != val2){
						factMatches = false;
						break;
					}
				}
				else if (constraint.type == VariableConstraint::Type::NOT_EQUAL)
				{
					if (val1 == val2){
						factMatches = false;
						break;
					}
				}
			}
	
		}

		/*if (totalFactTests % 10000 == 0)
			for (int x = 0; x < instance.getNumberOfActions(); x++)
				std::cerr << "Action " << x << " (" << instance.getAllActions()[x].name << "): " << futureReject[x] << " / " << futureTests[x] << "    " <<
				   htReject[x] << " / " << htTests[x] << std::endl;
*/

		if (!instance.allFutureSatisfiabilityDisabled && totalFactTests % 1000*1000 == 0 && totalFactTests){
			//std::cout << getPeakRSS() << " " << getCurrentRSS() << std::endl;
			size_t currentRSS = getCurrentRSS();
			if (currentRSS >= 3LL * 1024LL * 1024LL * 1024LL){
				if (!config.quietMode) std::cout << "Memory usage exceeds 3 GiB, dropping prediction data structures." << std::endl;
				if (!config.quietMode) std::cout << getPeakRSS() << " " << getCurrentRSS() << std::endl;
			
				// disable future precondition checking for all actions
				const_cast<InstanceType &>(instance).disableAllFutureSatisfiability();
				
				// clear the data structure
				stateMap.dropConsistencyTable();
				//stateMap.dropEligibleInitialPrecondition();

				if (!config.quietMode) std::cout << getPeakRSS() << " " << getCurrentRSS() << std::endl;
			}
		}
		
		if (futureTests[actionNo] % 100 == 0 && futureTests[actionNo]){
			const auto & action = instance.getAllActions()[actionNo];
			if (instance.pruneWithFutureSatisfiablility[actionNo] && futureReject[actionNo] < futureTests[actionNo] / 10){
				const_cast<InstanceType &>(instance).disablePruneWithFutureSatisfiablility(actionNo);
				if (!config.quietMode)
				   	std::cerr << " ---> Disabling potentially consistent extension checking for action:           " << actionNo << " (" << action.name << ")" << std::endl;
			}
		}



		if (false && htTests[actionNo] % 100 == 0 && htTests[actionNo]){
			const auto & action = instance.getAllActions()[actionNo];
			if (instance.pruneWithHierarchyTyping[actionNo] && htReject[actionNo] < htTests[actionNo] / 10){
				const_cast<InstanceType &>(instance).disablePruneWithHierarchyTyping(actionNo);
				if (!config.quietMode)
				   	std::cerr << " ---> Disabling hierarchy typing checking during match precondition for action: " << actionNo << " (" << action.name << ")" << std::endl;
			}
		}

		//if (config.printTimings && totalFactTests % 100000 == 0)
		//{
			// printStatistics(instance);
		//}

		if (factMatches)
		{
			foundExtension = true;
			matchedPreconditions[preconditionIdx] = stateElement.groundedNo;
			gpgMatchPrecondition (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStates, stateMap, actionNo, assignedVariables, initiallyMatchedPrecondition, initiallyMatchedState, matchedPreconditions, preconditionIdx + 1, config);
		}

		for (int newlyAssignedVar : newlyAssigned)
			assignedVariables.erase (newlyAssignedVar);
	}

	if (! foundExtension)
		noextensionFound[actionNo][preconditionIdx][initiallyMatchedPrecondition]++;
}


struct GpgTdg
{
	using StateType = GroundedTask;
	using ActionType = DecompositionMethod;
	using ResultType = GroundedMethod;
	using PreconditionType = TaskWithArguments;

	const Domain & domain;

	const Problem & problem;

	std::vector<GroundedTask *> & tasks;

	bool allFutureSatisfiabilityDisabled = false;
	std::vector<bool> pruneWithHierarchyTyping;
	std::vector<bool> pruneWithFutureSatisfiablility;

	GpgTdg (const Domain & domain, const Problem & problem, std::vector<GroundedTask *> & tasks) : domain (domain), problem (problem), tasks (tasks) {
		for (size_t i = 0; i < domain.decompositionMethods.size(); i++){
			pruneWithFutureSatisfiablility.push_back(true);
			pruneWithHierarchyTyping.push_back(true);
		}
	}
	int getInitialStateStart (void) 
	{
		// sort by task number
		std::sort(tasks.begin(), tasks.end(), [ ](const auto& lhs, const auto& rhs){ return lhs->taskNo < rhs->taskNo; });

		return 0;
	}

	void getInitialStateNext (int & it) 
	{
		delete tasks[it];
		it++;
	}

	const StateType & getInitialStateElement (int & it) 
	{
		return *tasks[it];
	}

	bool isInitialStateEnd (int it) const
	{
		return it == tasks.size();
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

	const std::string getAntecedantName(int antecedantHeadNo) const
	{
		return domain.tasks[antecedantHeadNo].name;
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
	
			// if the variable has already been assigned, the values must be consistent
			if (assignedVariables.isAssigned(taskVarIdx)){
				if (assignedVariables[taskVarIdx] != groundedTask.arguments[argIdx])
					return false;
			} else	
				assignedVariables[taskVarIdx] = groundedTask.arguments[argIdx];
		}

		if (outputVariableAssignment != NULL)
			*outputVariableAssignment = assignedVariables;

		return true;
	}

	void disableAllFutureSatisfiability(){
		allFutureSatisfiabilityDisabled = true;
		for (int a = 0; a < getNumberOfActions(); a++)
			disablePruneWithFutureSatisfiablility(a);
	}
	
	void disablePruneWithFutureSatisfiablility(size_t actionIdx){
		pruneWithFutureSatisfiablility[actionIdx] = false;
	}

	void disablePruneWithHierarchyTyping(size_t actionIdx){
		pruneWithHierarchyTyping[actionIdx] = false;
	}
};

/**
 * TODO
 */
template<GpgInstance InstanceType>
void runGpg (const InstanceType & instance, std::vector<typename InstanceType::ResultType *> & output, std::set<typename InstanceType::StateType> & outputStateElements,
		const HierarchyTyping * hierarchyTyping, 
		grounding_configuration & config)
{
	output.clear ();

	GpgPreprocessedDomain<InstanceType> preprocessed (instance, instance.domain, instance.problem);
	static GpgStateMap<InstanceType> stateMap (instance, preprocessed, config.futureCachingByPrecondition);

	GpgLiteralSet<typename InstanceType::StateType> processedStateElements (instance.getNumberOfPredicates ());

	// We need a queue to process new state elements in the correct order (which makes things faster),
	// and a set to prevent duplicate additions to the queue.
	std::queue<typename std::unordered_set<typename InstanceType::StateType>::const_iterator> toBeProcessedQueue;
	std::unordered_set<typename InstanceType::StateType> toBeProcessedSet;

	// Consider all facts from the initial state as not processed yet
	auto it = const_cast<InstanceType &>(instance).getInitialStateStart();
	while (!instance.isInitialStateEnd(it))
	//for (typename InstanceType::StateType initStateElement : instance.getInitialState ())
	{
		auto initStateElement = const_cast<InstanceType &>(instance).getInitialStateElement(it);
		// Number initial state elements
		initStateElement.groundedNo = toBeProcessedQueue.size ();

		DEBUG(std::cout << "New Fact " << initStateElement.groundedNo << ": " << initStateElement.getHeadNo();
		for (int arg : initStateElement.arguments) std::cout << " " << arg;
		std::cout << std::endl;
		);


		// Filter duplicate init state elements (seems to happen in some test cases?)
		if (toBeProcessedSet.count (initStateElement) == 0)
		{
			auto [it,_] = toBeProcessedSet.insert (initStateElement);
			toBeProcessedQueue.push (it);
		}

		// move to next
		const_cast<InstanceType &>(instance).getInitialStateNext(it);

		assert (toBeProcessedQueue.size () == toBeProcessedSet.size ());
	}


	// Reset counters
	totalFactTests = 0;
	totalFactHits = 0;
	
	htReject.clear(); htReject.resize(instance.getNumberOfActions());
	htTests.clear(); htTests.resize(instance.getNumberOfActions());
	futureReject.clear(); futureReject.resize(instance.getNumberOfActions());
	futureTests.clear(); futureTests.resize(instance.getNumberOfActions());
	
	stateElementGroundingTime.clear();
	stateElementMPTime.clear();
	stateElementInsertTime.clear();
	liftedGroundingTime.clear();
	instantiationtime.clear();
	instantiationtime2.clear();
	
	liftedGroundingCount.clear();
	factTests.clear ();
	factHits.clear ();
	factFutureRejects.clear ();
	
	factTests.resize (instance.getNumberOfActions ());
	factHits.resize (instance.getNumberOfActions ());
	factFutureRejects.resize (instance.getNumberOfActions ());
	noextensionFound.resize (instance.getNumberOfActions ());

	for (size_t i = 0; i < instance.getNumberOfActions (); ++i){
		factTests[i].resize (instance.getAllActions ()[i].getAntecedents ().size ());
		factHits[i].resize (instance.getAllActions ()[i].getAntecedents ().size ());
		factFutureRejects[i].resize (instance.getAllActions ()[i].getAntecedents ().size ());
		noextensionFound[i].resize (instance.getAllActions ()[i].getAntecedents ().size ());
		for (size_t j = 0; j < instance.getAllActions()[i].getAntecedents().size(); j++){
			factTests[i][j].resize (instance.getAllActions ()[i].getAntecedents ().size ());
			factHits[i][j].resize (instance.getAllActions ()[i].getAntecedents ().size ());
			factFutureRejects[i][j].resize (instance.getAllActions ()[i].getAntecedents ().size ());
			noextensionFound[i][j].resize (instance.getAllActions ()[i].getAntecedents ().size ());
		}
	}

	if (!config.quietMode) std::cerr << "Process actions without preconditions" << std::endl;

	// First, process all actions without preconditions
	for (int actionIdx = 0; actionIdx < instance.getNumberOfActions (); ++actionIdx)
	{
		const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];
		if (action.getAntecedents ().size () != 0)
			continue;

		VariableAssignment assignedVariables (action.variableSorts.size ());
		typename InstanceType::StateType f;
		std::vector<int> matchedPreconditions (action.getAntecedents ().size (), -1);
		gpgMatchPrecondition (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStateElements, stateMap, actionIdx, assignedVariables, 0, f, matchedPreconditions, 0, config);
	}
	
	if (!config.quietMode) std::cerr << "Done." << std::endl;

	while (!toBeProcessedQueue.empty ())
	{
		std::clock_t se_begin;
		if (!config.quietMode && config.printTimings) se_begin = std::clock();
		
		assert (toBeProcessedQueue.size () == toBeProcessedSet.size ());

		// Take any not-yet-processed state element
		const typename std::unordered_set<typename InstanceType::StateType>::const_iterator stateElementIterator = toBeProcessedQueue.front ();
		const typename InstanceType::StateType stateElement = *stateElementIterator;
		toBeProcessedQueue.pop();
		toBeProcessedSet.erase(stateElementIterator);

		const typename InstanceType::StateType * elementPointer = processedStateElements.insert (stateElement);
		std::clock_t c_start;
		if (!config.quietMode && config.printTimings) {
			//std::cout << stateElement.getHeadNo() << " ";	
			//std::cout << instance.getAntecedantName(stateElement.getHeadNo()) << std::endl;	
			c_start = std::clock();
		}
		
		stateMap.insertState (elementPointer);
		

		if (!config.quietMode && config.printTimings) {
			std::clock_t i_end = std::clock();
			double time_elapsed_ms = 1000.0 * (i_end-c_start) / CLOCKS_PER_SEC;
			stateElementInsertTime[stateElement.getHeadNo()] += time_elapsed_ms;
		}

		// Find tasks with this predicate as precondition
		for (const auto & [actionIdx, preconditionIdx] : preprocessed.preconditionsByPredicate[stateElement.getHeadNo ()])
		{
			if (!stateMap.hasInstanceForAllAntecedants(actionIdx,preconditionIdx))
				continue;

			const typename InstanceType::ActionType & action = instance.getAllActions ()[actionIdx];

			assert (action.getAntecedents ()[preconditionIdx].getHeadNo () == stateElement.getHeadNo ());

			VariableAssignment assignedVariables (action.variableSorts.size ());
			if (!instance.doesStateFulfillPrecondition (action, &assignedVariables, stateElement, preconditionIdx))
				continue;
		
			if (instance.pruneWithFutureSatisfiablility[actionIdx] && action.getAntecedents().size() != 1 &&
					!stateMap.hasPotentiallyConsistentExtension(actionIdx, -1, assignedVariables, preconditionIdx))
				continue;
			
			if (instance.pruneWithHierarchyTyping[actionIdx] && hierarchyTyping != nullptr &&
					!hierarchyTyping->isAssignmentCompatible<typename InstanceType::ActionType> (actionIdx, assignedVariables))
				continue;
			
			std::clock_t cc_begin;
		   	if (!config.quietMode && config.printTimings) cc_begin = std::clock();

			std::vector<int> matchedPreconditions (action.getAntecedents ().size (), -1);
			matchedPreconditions[preconditionIdx] = stateElement.groundedNo;
			gpgMatchPrecondition (instance, hierarchyTyping, output, toBeProcessedQueue, toBeProcessedSet, processedStateElements, stateMap, actionIdx, assignedVariables, preconditionIdx, stateElement, matchedPreconditions, 0, config);
			
			if (!config.quietMode && config.printTimings){
				std::clock_t cc_end = std::clock();
				double time_elapsed_ms = 1000.0 * (cc_end-cc_begin) / CLOCKS_PER_SEC;
				liftedGroundingTime[actionIdx] += time_elapsed_ms;
				stateElementMPTime[stateElement.getHeadNo()] += time_elapsed_ms;
			}
		}

		if (!config.quietMode && config.printTimings){
			//std::clock_t c_end = std::clock();
			//std::cout << toBeProcessedQueue.size() << " " << output.size() << std::endl;

			//double time_elapsed_ms = 1000.0 * (c_end-c_start) / CLOCKS_PER_SEC;
			//std::cout << "CPU time used: " << time_elapsed_ms << " ms\n";
		}
		
		if (!config.quietMode && config.printTimings){
			std::clock_t se_end = std::clock();
			double time_elapsed_ms = 1000.0 * (se_end-se_begin) / CLOCKS_PER_SEC;
			stateElementGroundingTime[stateElement.getHeadNo()] += time_elapsed_ms;
		}

	}

	outputStateElements = processedStateElements;

	if (!config.quietMode && config.printTimings) printStatistics(instance);
	if (!config.quietMode) std::cerr << "Returning from runGpg()." << std::endl;
}


void tdgDfs (std::vector<GroundedTask> & outputTasks, std::vector<GroundedMethod> & outputMethods, std::vector<GroundedTask*> & inputTasks, std::vector<GroundedMethod*> & inputMethods, std::vector<Fact> & reachableFactsList, std::unordered_set<int> & reachableCEGuards, const Domain & domain, const Problem & problem);



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
void validateGroundedListP (const std::vector<T*> & input)
{
	for (size_t i = 0; i < input.size (); ++i)
	{
		if (input[i]->groundedNo != i)
		{
			std::cout << "Grounded object list is inconsistent: entry " << i << " has grounded number " << input[i]->groundedNo << std::endl;
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


/**
 * @}
 */

#endif
