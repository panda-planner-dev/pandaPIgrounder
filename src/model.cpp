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

void Fact::setHeadNo (int headNo)
{
	predicateNo = headNo;
}

int Fact::getHeadNo (void) const
{
	return predicateNo;
}

bool Fact::operator < (const Fact & other) const
{
	return std::tie (predicateNo, arguments) < std::tie (other.predicateNo, other.arguments);
}

bool Fact::operator == (const Fact & other) const
{
	return std::tie (predicateNo, arguments) == std::tie (other.predicateNo, other.arguments);
}

void PredicateWithArguments::setHeadNo (int headNo)
{
	predicateNo = headNo;
}

int PredicateWithArguments::getHeadNo (void) const
{
	return predicateNo;
}

void TaskWithArguments::setHeadNo (int headNo)
{
	taskNo = headNo;
}

int TaskWithArguments::getHeadNo (void) const
{
	return taskNo;
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

		// if the variable has already been assigned, the values must be consistent
		if (assignedVariables.isAssigned(taskVarIdx)){
			if (assignedVariables[taskVarIdx] != fact.arguments[argIdx])
				return false;
		} else	
			assignedVariables[taskVarIdx] = fact.arguments[argIdx];
	}

	if (outputVariableAssignment != NULL)
		*outputVariableAssignment = assignedVariables;

	return true;
}

int Task::computeGroundCost(GroundedTask & task,std::map<Fact,int> & init_functions_map) const
{
	// compute the costs for this ground actions
	std::vector<std::variant<PredicateWithArguments,int>> additive_cost_expressions = this->costs;
	int costs = 0;
	for (std::variant<PredicateWithArguments,int> cost_element : additive_cost_expressions){
		if (std::holds_alternative<int>(cost_element)){
			costs += std::get<int>(cost_element);
		} else {
			PredicateWithArguments function_term = std::get<PredicateWithArguments>(cost_element);
			// build fact representation of this term with respect to the grounding
			Fact cost_fact;
			cost_fact.predicateNo = function_term.predicateNo;
			for (int & argument_variable : function_term.arguments)
				cost_fact.arguments.push_back(task.arguments[argument_variable]);
			
			costs += init_functions_map[cost_fact];
		}
	}
	return costs;
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

const std::vector<TaskWithArguments> & DecompositionMethod::getAntecedents (void) const
{
	return subtasks;
}

const std::vector<TaskWithArguments> DecompositionMethod::getConsequences (void) const
{
	std::vector<TaskWithArguments> consequences;
	TaskWithArguments consequence;
	consequence.taskNo = taskNo;
	consequence.arguments = taskParameters;
	consequences.push_back (consequence);
	return consequences;
}

const std::vector<PredicateWithArguments> & Task::getAntecedents (void) const
{
	return preconditions;
}

const std::vector<PredicateWithArguments> & Task::getConsequences (void) const
{
	return effectsAdd;
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

const Fact & FactSet::find (const Fact & fact) const
{
	assert (fact.predicateNo < factsByPredicate.size ());

	return * factsByPredicate[fact.predicateNo].find (fact);
}

void FactSet::insert (const Fact & fact)
{
	assert (fact.predicateNo < factsByPredicate.size ());

	factsByPredicate[fact.predicateNo].insert (fact);
}

void FactSet::erase (const Fact & fact)
{
	assert (fact.predicateNo < factsByPredicate.size ());

	factsByPredicate[fact.predicateNo].erase (fact);
}

const std::set<Fact> & FactSet::getFactsForPredicate (int predicateNo) const
{
	assert (predicateNo < factsByPredicate.size ());

	return factsByPredicate[predicateNo];
}

FactSet::operator std::set<Fact> (void) const
{
	std::set<Fact> result;
	for (const auto & predicateFacts : factsByPredicate)
		result.insert (predicateFacts.begin (), predicateFacts.end ());
	return result;
}

void GroundedTask::setHeadNo (int headNo)
{
	taskNo = headNo;
}

int GroundedTask::getHeadNo (void) const
{
	return taskNo;
}

bool GroundedTask::operator < (const GroundedTask & other) const
{
	return std::tie (taskNo, arguments) < std::tie (other.taskNo, other.arguments);
}

bool GroundedTask::operator == (const GroundedTask & other) const
{
	return std::tie (taskNo, arguments) == std::tie (other.taskNo, other.arguments);
}


void GroundedMethod::setHeadNo (int headNo)
{
	methodNo = headNo;
}

int GroundedMethod::getHeadNo (void) const
{
	return methodNo;
}

bool GroundedMethod::operator < (const GroundedMethod & other) const
{
	return std::tie (methodNo, arguments) < std::tie (other.methodNo, other.arguments);
}

bool GroundedMethod::operator == (const GroundedMethod & other) const
{
	return std::tie (methodNo, arguments) == std::tie (other.methodNo, other.arguments);
}


	
