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

	VariableAssignment assignedVariables;
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
