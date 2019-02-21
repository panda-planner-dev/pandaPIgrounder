#include <algorithm>
#include <numeric>
#include <string>
#include <tuple>

#include <cassert>

#include "model.h"

BadInputException::BadInputException (std::string message) : message (message)
{
}

const char * BadInputException::what () const throw ()
{
	return message.c_str ();
}

bool Fact::operator < (const Fact & other) const
{
	return std::tie (predicateNo, arguments) < std::tie (other.predicateNo, other.arguments);
}

bool Fact::operator == (const Fact & other) const
{
	return std::tie (predicateNo, arguments) == std::tie (other.predicateNo, other.arguments);
}

bool Task::doesFactFulfilPrecondition (VariableAssignment * outputVariableAssignment, const Domain & domain, const Fact & fact, int preconditionIdx) const
{
	const PredicateWithArguments & precondition = preconditions[preconditionIdx];

	// The predicate of the fact and the precondition must match
	if (precondition.predicateNo != fact.predicateNo)
		return false;

	assert (fact.arguments.size () == domain.predicates[fact.predicateNo].argumentSorts.size ());
	assert (fact.arguments.size () == precondition.arguments.size ());

	VariableAssignment assignedVariables (variableSorts.size ());
	for (size_t argIdx = 0; argIdx < precondition.arguments.size (); ++argIdx)
	{
		int taskVarIdx = precondition.arguments[argIdx];
		int argumentSort = variableSorts[taskVarIdx];

		// Make sure that the argument to the fact matches the task's variable.
		// E.g. we could have a fact like "+at truck-0 city-loc-0", but this task could have
		// "+at ?var1 ?var2" as a precondition, where ?var1 must be a package (and not a truck).
		if (domain.sorts[argumentSort].members.count (fact.arguments[argIdx]) == 0)
			return false;

		assignedVariables[taskVarIdx] = fact.arguments[argIdx];
	}

	if (outputVariableAssignment != NULL)
		*outputVariableAssignment = assignedVariables;

	return true;
}

VariableAssignment::VariableAssignment (size_t nVariables) : assignments (nVariables, NOT_ASSIGNED)
{
}

int & VariableAssignment::operator [] (int varIdx)
{
	assert (varIdx >= 0 && varIdx < assignments.size ());

	return assignments[varIdx];
}

int VariableAssignment::operator[] (int varIdx) const
{
	assert (varIdx >= 0 && varIdx < assignments.size ());

	return assignments[varIdx];
}

void VariableAssignment::assign (int varIdx, int value)
{
	assert (varIdx >= 0 && varIdx < assignments.size ());
	assert (value >= 0);

	assignments[varIdx] = value;
}

bool VariableAssignment::isAssigned (int varIdx) const
{
	assert (varIdx >= 0 && varIdx < assignments.size ());

	return assignments[varIdx] != NOT_ASSIGNED;
}

size_t VariableAssignment::size (void) const
{
	return assignments.size () - std::count (assignments.begin (), assignments.end (), NOT_ASSIGNED);
}

void VariableAssignment::erase (int varIdx)
{
	assert (varIdx >= 0 && varIdx < assignments.size ());

	assignments[varIdx] = NOT_ASSIGNED;
}

VariableAssignment::operator std::vector<int> (void) const
{
	return assignments;
}

FactSet::FactSet (size_t nPredicates) : factsByPredicate (nPredicates)
{
}

size_t FactSet::size (void) const
{
	return std::accumulate (factsByPredicate.begin (), factsByPredicate.end (), 0, [](const int & acc, const auto & factSet) { return acc + factSet.size (); });
}

size_t FactSet::count (const Fact & fact) const
{
	assert (fact.predicateNo < factsByPredicate.size ());

	return factsByPredicate[fact.predicateNo].count (fact);
}

void FactSet::insert (const Fact & fact)
{
	assert (fact.predicateNo < factsByPredicate.size ());

	factsByPredicate[fact.predicateNo].insert (fact);
}

const std::set<Fact> & FactSet::getFactsForPredicate (int predicateNo) const
{
	assert (predicateNo < factsByPredicate.size ());

	return factsByPredicate[predicateNo];
}

FactSet::operator std::set<Fact> (void) const
{
	std::set<Fact> result;
	for (auto predicateFacts : factsByPredicate)
		result.insert (predicateFacts.begin (), predicateFacts.end ());
	return result;
}
