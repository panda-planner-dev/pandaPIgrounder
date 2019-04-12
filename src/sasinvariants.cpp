#include <algorithm>
#include <iostream>
#include <set>
#include <unordered_set>
#include <vector>
#include <map>
#include <cassert>

#include "debug.h"
#include "model.h"
#include "sasinvariants.h"


struct unifier{
	std::map<int,int> unionFind;

	int get(int i){
		if (unionFind.count(i) == 0) unionFind[i] = i;
		if (unionFind[i] == i) return i;
		return get(unionFind[i]);
	}

	void varunion(int i, int j){
		i = get(i);
		j = get(j);
		unionFind[i] = j;
	}
};

struct invariantCandidate{
	// variables in invariant candidate are numbered -1, -2, -3, ... to keep them distinct from variables in tasks!
	std::set<int> fixedVariables; // those set fixed in the mutex group
	std::set<int> freeVariables; // those over which we quantify, also called "counted variables"
	std::vector<PredicateWithArguments> elements;

	int nextFreeVariable() {return - int(fixedVariables.size()) - int(freeVariables.size()) - 1; }
	bool predicateIsContained(int predicate){
		for (auto & element : elements) if (element.predicateNo == predicate) return true;
		return false;
	}

    bool operator==(const invariantCandidate& other) const {
		if (elements.size() < other.elements.size()) return false;
		if (fixedVariables.size() < other.fixedVariables.size()) return false;
		if (freeVariables.size() < other.freeVariables.size()) return false;
		
		std::vector<int> mapping;
		for (unsigned int i = 0; i < fixedVariables.size() + freeVariables.size(); i++)
			mapping.push_back(-int(i)-1);
		std::sort(mapping.begin(), mapping.end());

		//std::cerr << "iso " << std::endl;
		do {
			bool failed = false;
			//std::cerr << "mapping:";
			//for (unsigned int i = 0; i < fixedVariables.size() + freeVariables.size(); i++) std::cerr << " " << -int(i)-1 << " -> " << mapping[i];
			//std::cerr << std::endl;

			// check correct grouping
			for (const int & fixed : fixedVariables) if (other.fixedVariables.count(mapping[-fixed-1]) == 0) failed = true;
			//std::cerr << "F " << std::boolalpha << failed << std::endl;
			// free variables are ok, as the number is the same
			for (const auto & myElement : elements){
				bool found = false;
				for (const auto & otherElement : other.elements){
					if (myElement.predicateNo != otherElement.predicateNo) continue;
					bool match = true;
					for (unsigned int i = 0; i < myElement.arguments.size(); i++){
						int translated = mapping[-myElement.arguments[i] - 1];
						match &= otherElement.arguments[i] == translated;
					}
					if (!match) continue;
					found = true;
					break;
				}
				//std::cerr << "Found " << std::boolalpha << found << std::endl;
				if (found) continue;
				failed = true;
				break;
			}
			//std::cerr << "F " << std::boolalpha << failed << std::endl;
			// if we have not failed, this mapping is an isomorphism
			if (!failed) return true;
		} while(std::next_permutation(mapping.begin(), mapping.end()));
        return false;
    };

    size_t operator()(const invariantCandidate& toHash) const noexcept {
        size_t hash = toHash.elements.size() * 100 * 100 + toHash.fixedVariables.size() * 100 + toHash.freeVariables.size();
		for (const auto & element : toHash.elements) hash += element.predicateNo * 100 * 100 * 100;
		//std::cerr << "HASH " << hash << std::endl;
        return hash;
    };
};

void printInvariant(const Domain & domain, const invariantCandidate & candidate){
	std::cerr << "invariant: ";
	for (const int & var : candidate.fixedVariables) std::cerr << " " << var;
	std::cerr << ":";
	for (const auto & element : candidate.elements) {
		std::cerr << " " << domain.predicates[element.predicateNo].name << "(";
		for (unsigned int i = 0; i < element.arguments.size(); i++) {
			if (i) std::cerr << " ";
			std::cerr << element.arguments[i];
		}
		std::cerr << ")";
	}
	std::cerr << std::endl;
}


/**
 * Computes a unifier for pred1 and pred2 so that all fixed variables are unified.
 *
 * Extends a previously existing unifier and copies it.
 */
// assumption: pred2 is part of the candidate!
unifier unifyUnderCandidate(unifier currentUnifier, PredicateWithArguments pred1, PredicateWithArguments pred2, invariantCandidate candidate){
	assert(pred1.predicateNo == pred2.predicateNo);
	unifier newUnifier = currentUnifier;

	for (unsigned int i = 0; i < pred1.arguments.size(); i++){
		int var1 = pred1.arguments[i];
		int var2 = pred2.arguments[i];
		if (candidate.fixedVariables.count(var2))
			newUnifier.varunion(var1,var2);
	}

	return newUnifier;
}

bool isDifferent(unifier & currentUnifier, const PredicateWithArguments & pred1, const PredicateWithArguments & pred2){
	if (pred1.predicateNo != pred2.predicateNo) return true;

	for (unsigned int k = 0; k < pred1.arguments.size(); k++)
		if (currentUnifier.get(pred1.arguments[k]) != currentUnifier.get(pred2.arguments[k])) return true;
	
	return false;
}

/**
 * Checks whether the task taskNo can possibly adds two of the elements of the candidate
 */
bool tooHeavy(const Domain & domain, int taskNo, invariantCandidate & candidate){

	for (const auto & element1 : candidate.elements){
		// go through all pairs of different add effects
		for (unsigned int i = 0; i < domain.tasks[taskNo].effectsAdd.size(); i++){
			const PredicateWithArguments & add1 = domain.tasks[taskNo].effectsAdd[i];
			if (element1.predicateNo != add1.predicateNo) continue;
	
			unifier add1Unifier; add1Unifier = unifyUnderCandidate(add1Unifier, add1, element1, candidate); 
	
			for (const auto & element2 : candidate.elements){
				for (unsigned int j = i+1; j < domain.tasks[taskNo].effectsAdd.size(); j++){
					const PredicateWithArguments & add2 = domain.tasks[taskNo].effectsAdd[j];
					if (element2.predicateNo != add2.predicateNo) continue;
					unifier add2Unifier = unifyUnderCandidate(add1Unifier, add2, element2, candidate); 
					
					// add1 and add2 are now unified according to the fixed variables in a candidate, check whether they are actually different
					if (!isDifferent(add2Unifier, add1, add2)) continue; // not different under unification so: can't cause too heavy
					// can't be too heavy if contained in prec, as this will not add anything
					for (const auto & prec : domain.tasks[taskNo].preconditions)
						if (!isDifferent(add2Unifier, add1, prec) || ! isDifferent(add2Unifier, add2, prec)) goto not_too_heavy;
						
					// TODO: whether unifier or coverage of free/counted variables implies that constraints are broken

					return true;

					not_too_heavy: ;
				}
			}
		}
	}
	return false;
}

bool tooHeavy(const Domain & domain, invariantCandidate & candidate){
	for (int taskNo = 0; taskNo < domain.nPrimitiveTasks; taskNo++)
		if (tooHeavy(domain, taskNo, candidate)) return true;
	return false;
}


bool isCovered(unifier currentUnifier, const PredicateWithArguments & pred, invariantCandidate & candidate){
	for (const auto & element : candidate.elements){
		if (pred.predicateNo != element.predicateNo) continue;
		// check whether all fixed variables are necessarily the same
		for (unsigned int i = 0; i < element.arguments.size(); i++)
			if (candidate.fixedVariables.count(element.arguments[i]) && currentUnifier.get(element.arguments[i]) != currentUnifier.get(pred.arguments[i])) goto no_good;

		// TODO: this currently ignores variable constraints ...
		
		return true;

		no_good: ;
	}
	return false;
}

struct repair{
	int delEffectNo;
	unifier addUnifier;
};

bool isAddEffectUnbalanced(const Domain & domain, int taskNo, int addEffectNo, const PredicateWithArguments & element, invariantCandidate & candidate, std::vector<repair> & repairs){
	const PredicateWithArguments & add = domain.tasks[taskNo].effectsAdd[addEffectNo];
	unifier addUnifier; addUnifier = unifyUnderCandidate(addUnifier, add, element, candidate);
	// find possible balancing del effect
	for (unsigned int i = 0; i < domain.tasks[taskNo].effectsDel.size(); i++){
		const PredicateWithArguments & del = domain.tasks[taskNo].effectsDel[i];
		if (! isDifferent(addUnifier, add, del)) continue; // add takes precedence over del, this cannot be repaired
		if (! isCovered(addUnifier, del, candidate)) {
			// this could be repaired by adding the del effect to the candidate
			repair rep;
			rep.delEffectNo = i;
			rep.addUnifier = addUnifier;
			repairs.push_back(rep);
			continue;
		}
		// this del effect does not necessarily remove something from the invariant set
		// find precondition that asserts that del is true
		for (unsigned int j = 0; j < domain.tasks[taskNo].preconditions.size(); j++)
			if (! isDifferent(addUnifier,del,domain.tasks[taskNo].preconditions[j])) return false;
		// if non is found I think this cannot be repaired
	}
	return true;
}

bool isAddEffectUnbalanced(const Domain & domain, int taskNo, int addEffectNo, invariantCandidate & candidate, std::vector<repair> & repairs){
	const PredicateWithArguments & add = domain.tasks[taskNo].effectsAdd[addEffectNo];

	for (const auto & element : candidate.elements){
		if (add.predicateNo != element.predicateNo) continue;
		repairs.clear();
		if (isAddEffectUnbalanced(domain, taskNo, addEffectNo, element, candidate, repairs)) return true;
	}
	return false;
}

int getUnbalancedAddEffect(const Domain & domain, int taskNo, invariantCandidate & candidate, std::vector<repair> & repairs){
	for (unsigned int i = 0; i < domain.tasks[taskNo].effectsAdd.size(); i++){
		const PredicateWithArguments & add = domain.tasks[taskNo].effectsAdd[i];
		if (! candidate.predicateIsContained(add.predicateNo)) continue;
		if (isAddEffectUnbalanced(domain,taskNo,i,candidate, repairs)) return i;
	}
	return -1; // none
}



void invariantSearch(const Domain & domain, invariantCandidate & candidate, std::unordered_set<invariantCandidate, invariantCandidate> & closedList, std::set<int> & flexible, std::vector<invariant> & invariants){
	if (closedList.count(candidate)) return; // this candidate has already been visited
	closedList.insert(candidate);
	DEBUG( printInvariant(domain,candidate) );

	if (tooHeavy(domain,candidate)) return; // cannot be fixed
	for (int taskNo = 0; taskNo < domain.nPrimitiveTasks; taskNo++){
		std::vector<repair> repairs;
		int unbalanced = getUnbalancedAddEffect(domain, taskNo, candidate, repairs);
		if (unbalanced == -1) continue; // application does not violate invariant
		DEBUG( std::cerr << "\tTask [" << taskNo << "] " << domain.tasks[taskNo].name << " is unbalanced on add effect " <<
				domain.predicates[domain.tasks[taskNo].effectsAdd[unbalanced].predicateNo].name << std::endl );
		// try to find a repair
		for (repair r : repairs){
			const PredicateWithArguments & del = domain.tasks[taskNo].effectsDel[r.delEffectNo];
			const int & predicate = del.predicateNo;
			if (flexible.count(predicate) == 0) continue; // don't consider rigid predicates
			DEBUG( std::cerr << "\tPotential repair on del effect " << 
				domain.predicates[domain.tasks[taskNo].effectsDel[r.delEffectNo].predicateNo].name << std::endl );

			// at most one new variable, only fixed variables are so far unified
			// at the same time: build the new element
			int unboundVariableCount = 0;
			PredicateWithArguments newElement; newElement.predicateNo = predicate;
			for (unsigned int delArg = 0; delArg < del.arguments.size(); delArg++){
				// find equal fixed variable
				int foundVar = 0;
				for (const int & fixedVar : candidate.fixedVariables)
					if (r.addUnifier.get(fixedVar) == r.addUnifier.get(del.arguments[delArg])) foundVar = fixedVar;

				if (foundVar == 0){
					unboundVariableCount++;
					foundVar = candidate.nextFreeVariable();
				}

				newElement.arguments.push_back(foundVar);
			}

			// should always be > 0, right?
			if (unboundVariableCount <= 1){
				// check if not contained
				bool contained = false;
				int	superceded = -1;
				for (unsigned int elemNo = 0; elemNo < candidate.elements.size(); elemNo++){
					const auto & element = candidate.elements[elemNo];
					if (element.predicateNo != predicate) continue;
					bool equalOrDominated = true;
					bool superceding = true;
					for (unsigned int i = 0; i < element.arguments.size() && equalOrDominated; i++){
						if (candidate.fixedVariables.count(element.arguments[i]) && candidate.fixedVariables.count(newElement.arguments[i])){
							// both are fixed, then equal if vars are equal
							equalOrDominated = element.arguments[i] == newElement.arguments[i];
						} else if (candidate.fixedVariables.count(newElement.arguments[i])) equalOrDominated = false;
						else if (candidate.fixedVariables.count(element.arguments[i])) superceding = false;
					}
					if (!equalOrDominated && !superceding) continue;
					if (equalOrDominated) contained = true;
					if (superceding) superceded = elemNo;
					break;
				}
				
				if (contained) continue;

				invariantCandidate newCandidate = candidate;
				if (superceded != -1) candidate.elements.erase(candidate.elements.begin() + superceded);
				if (unboundVariableCount == 1) newCandidate.freeVariables.insert(newCandidate.nextFreeVariable());
				newCandidate.elements.push_back(newElement);
				// start the search
				invariantSearch(domain, newCandidate, closedList, flexible, invariants);
			}
		}

		return;
	}
	// found invariant
	DEBUG( std::cerr << "Found " );
	DEBUG( printInvariant(domain,candidate) );
	invariant newInvariant;
	newInvariant.fixedVariables = candidate.fixedVariables;
	newInvariant.freeVariables = candidate.freeVariables;
	newInvariant.elements = candidate.elements;

	invariants.push_back(newInvariant);
}


std::vector<invariant> computeSASPlusInvariants  (const Domain & domain, const Problem & problem){
	DEBUG (std::cerr << "Computing SAS+ invariants" << std::endl);
	
	/*invariantCandidate can;
	can.fixedVariables.insert(-1);
	can.freeVariables. insert(-2);
	can.freeVariables. insert(-3);
	PredicateWithArguments _temp;
	_temp.predicateNo = 1; // +at
	_temp.arguments.push_back(-1);
	_temp.arguments.push_back(-2);
	can.elements.push_back(_temp);
	_temp.predicateNo = 2; // +in
	_temp.arguments[0] = (-1);
	_temp.arguments[1] = (-3);
	can.elements.push_back(_temp);

	std::cerr << "too heavy: " << std::boolalpha << tooHeavy(domain, can) << std::endl;
	std::cerr << "unbalanced: " << std::endl;
	for (int taskNo = 0; taskNo < domain.nPrimitiveTasks; taskNo++){
		std::vector<int> unbalanced =  getUnbalancedAddEffects(domain, taskNo, can);
		std::cerr << "Task: " << domain.tasks[taskNo].name << ":";
		for(const int & addEffectNo : unbalanced) std::cerr << " " << addEffectNo << " " << domain.predicates[domain.tasks[taskNo].effectsAdd[addEffectNo].predicateNo].name;
		std::cerr << std::endl;
	}*/


	std::unordered_set<invariantCandidate, invariantCandidate> closedList;

	/*invariantCandidate can;
	can.fixedVariables.insert(-1);
	can.freeVariables. insert(-2);
	can.freeVariables. insert(-3);
	PredicateWithArguments _temp;
	_temp.predicateNo = 1; // +at
	_temp.arguments.push_back(-1);
	_temp.arguments.push_back(-2);
	can.elements.push_back(_temp);
	_temp.predicateNo = 2; // +in
	_temp.arguments[0] = (-1);
	_temp.arguments[1] = (-3);
	can.elements.push_back(_temp);

	closedList.insert(can);
	can.elements[0].arguments[1] = -3;
	can.elements[1].arguments[1] = -2;
	closedList.insert(can);
	can.elements[0].arguments[1] = -2;
	can.elements[1].arguments[1] = -2;
	closedList.insert(can);

	std::cerr << "SIZE " << closedList.size() << std::endl;
	exit(0);*/

	// create initial candidates
	std::set<int> flexible;
	for (unsigned int predicateNo = 0; predicateNo < domain.predicates.size(); predicateNo++){
		bool isRigid = true;
		for (int taskNo = 0; taskNo < domain.nPrimitiveTasks && isRigid; taskNo++){
			for (unsigned int i = 0; i < domain.tasks[taskNo].effectsAdd.size() && isRigid; i++) isRigid &= domain.tasks[taskNo].effectsAdd[i].predicateNo != int(predicateNo);
			for (unsigned int i = 0; i < domain.tasks[taskNo].effectsDel.size() && isRigid; i++) isRigid &= domain.tasks[taskNo].effectsDel[i].predicateNo != int(predicateNo);
		}
		if (isRigid) continue;
		flexible.insert(predicateNo);
	}

	std::vector<invariant> invariants;
	for (const int & predicateNo : flexible) {
		DEBUG (std::cerr << std::endl << "Found non-rigid predicate [" << predicateNo << "] " << domain.predicates[predicateNo].name << std::endl);

		invariantCandidate candidate;
		PredicateWithArguments predicate;
		predicate.predicateNo = predicateNo;
		for (unsigned int argumentNo = 0; argumentNo < domain.predicates[predicateNo].argumentSorts.size(); argumentNo++){
			int nextVar = candidate.nextFreeVariable();
			candidate.fixedVariables.insert(nextVar);
			predicate.arguments.push_back(nextVar);
		}
		candidate.elements.push_back(predicate);

		invariantSearch(domain, candidate, closedList, flexible, invariants);

		for (const int & var : predicate.arguments){
			candidate.fixedVariables.erase(var);
			candidate.freeVariables.insert(var);
			invariantSearch(domain, candidate, closedList, flexible, invariants);
			candidate.fixedVariables.insert(var);
			candidate.freeVariables.erase(var);
		}
	}

	return invariants;
}
