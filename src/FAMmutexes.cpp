#include <string>
#include <iostream>
#include <algorithm>
#include <cassert>

#include "debug.h"
#include "FAMmutexes.h"
#include "pddl/pddl.h"


// CPDDL has dome defined functions that we simply copy. They should be static to not clutter the name space (their library contains them as well, but I want to have them in an extra file)
#include "cpddl.h"


// BOR_ERR_INIT produces gcc warnings which I cannot change ...
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"


bool replacement_type_dfs(int cur, int end, std::set<int> & visited, std::vector<std::set<int>> & parents){
	if (cur == end) return true;
	if (!parents[cur].size()) return false;
	
	if (visited.count(cur)) return true;
	visited.insert(cur);

	for (int p : parents[cur])
		if (!replacement_type_dfs(p,end,visited,parents)) return false;

	return true;
}


std::pair<int,std::set<int>> get_replacement_type(int type_to_replace, std::vector<std::set<int>> & parents){
	// try all possible replacement sorts
	std::set<int> best_visited;
	int best_replacement = -1;
	for (size_t s = 0; s < parents.size(); s++) if (s != type_to_replace){
		std::set<int> visited;
		if (replacement_type_dfs(type_to_replace, s, visited, parents))
			if (best_replacement == -1 || best_visited.size() > visited.size()){
				best_replacement = s;
				best_visited = visited;
			}
	}

	return std::make_pair(best_replacement, best_visited);
}


std::tuple<std::vector<int>,std::vector<int>,std::map<int,int>> compute_local_type_hierarchy(const Domain & domain, const Problem & problem, grounding_configuration & config){
	// find subset relations between sorts
	
	// [i][j] = true means that j is a subset of i
	std::vector<std::vector<bool>> subset (domain.sorts.size());
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		if (!domain.sorts[s1].members.size()) {
			for (size_t s2 = 0; s2 < domain.sorts.size(); s2++) subset[s1].push_back(false);
			continue;
		}

		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++){
			if (s1 != s2 && domain.sorts[s2].members.size()){
				if (std::includes(domain.sorts[s1].members.begin(), domain.sorts[s1].members.end(),
							domain.sorts[s2].members.begin(), domain.sorts[s2].members.end())){
					// here we know that s2 is a subset of s1
					subset[s1].push_back(true);
				} else
					subset[s1].push_back(false);
			} else subset[s1].push_back(false);
		}
	}

	// transitive reduction
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			for (size_t s3 = 0; s3 < domain.sorts.size(); s3++)
				if (subset[s2][s1] && subset[s1][s3])
					subset[s2][s3] = false;
	
	
	DEBUG(for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++){
			if (subset[s1][s2]){
				std::cout << domain.sorts[s2].name;
				std::cout << " is a subset of ";
				std::cout << domain.sorts[s1].name;
				std::cout << std::endl;
			
			}
		}
	});

	// output as a DOT file
	DEBUG(
	 std::cout << "digraph sortgraph{" << std::endl;
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++){
			if (subset[s1][s2]){
				std::cout << "\t";
				std::cout << domain.sorts[s2].name;
				std::cout << " -> ";
				std::cout << domain.sorts[s1].name;
				std::cout << std::endl;
			
			}
		}
	}
	std::cout << "}" << std::endl;
	);


	// determine parents
	std::vector<std::set<int>> parents (domain.sorts.size());
	std::vector<int> parent (domain.sorts.size());
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		parent[s1] = -1;
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			if (subset[s1][s2]){
				parents[s2].insert(s1);
				if (parent[s2] != -1){
					if (parent[s2] >= 0 && !config.quietMode) 
						std::cout << "Type hierarchy is not a tree ... cpddl can't handle this. I have to compile ..." << std::endl;
					parent[s2] = -2;
				} else {
					parent[s2] = s1;
				}
			}


	DEBUG(for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		std::cout << domain.sorts[s1].name;
   		if (parent[s1] == -2) {	
			std::cout << " - {";
			for (int s : parents[s1])
				std::cout << domain.sorts[s].name << " ";
			std::cout << "}";

		} else if (parent[s1] != -1)
			std::cout << " - " << domain.sorts[parent[s1]].name;
		std::cout << std::endl; 
	});

	// sorts with multiple parents need to be replaced by parent sorts ...
	std::map<int,int> replacedSorts;
	
	for (size_t s = 0; s < domain.sorts.size(); s++) if (parent[s] == -2){
		DEBUG(std::cout << "Sort " << domain.sorts[s].name << " has multiple parents and must be replaced." << std::endl);
		auto [replacement, all_covered] = get_replacement_type(s,parents);
		assert(replacement != -1); // there is always the object type
		DEBUG(std::cout << "Replacement sort is " << domain.sorts[replacement].name << std::endl);
		DEBUG(std::cout << "All to be replaced:"; for (int ss : all_covered) std::cout << " " << domain.sorts[ss].name; std::cout << std::endl);

		for (int covered : all_covered){
			replacedSorts[covered] = replacement;
			parent[covered] = -2;
		}
	}

	// update parent relation
	for (size_t s = 0; s < domain.sorts.size(); s++) if (parent[s] >= 0){
		if (replacedSorts.count(parent[s]))
			parent[s] = replacedSorts[parent[s]];
	}

	// who is whose direct subset, with handling the replaced sorts
	std::vector<std::unordered_set<int>> directsubset (domain.sorts.size());
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++) if (parent[s2] >= 0)
			if (subset[s1][s2]){
				if (replacedSorts.count(s1))
					directsubset[replacedSorts[s1]].insert(s2);
				else
					directsubset[s1].insert(s2);
			}

	DEBUG(
		for (size_t s1 = 0; s1 < domain.sorts.size(); s1++) if (parent[s1] != -2){
			std::cout << "Direct subsorts of " << domain.sorts[s1].name << ":";
			for (int s : directsubset[s1]) std::cout << " " << domain.sorts[s].name;
			std::cout << std::endl;
		}
		);

	// assign elements to sorts
	std::vector<std::set<int>> directElements (domain.sorts.size());
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++) if (parent[s1] != -2){
		for (int elem : domain.sorts[s1].members){
			bool in_sub_sort = false;
			for (int s2 : directsubset[s1]){
				if (domain.sorts[s2].members.count(elem)){
					in_sub_sort = true;
					break;
				}
			}
			if (in_sub_sort) continue;
			directElements[s1].insert(elem);
		}
	}
	
	DEBUG(for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		std::cout << "Sort Elements: " << domain.sorts[s1].name << ":";
		for (int e : directElements[s1]) std::cout << " " << domain.constants[e];
		std::cout << std::endl;
	});

	std::vector<int> sortOfElement (domain.constants.size());
	for (size_t c = 0; c < domain.constants.size(); c++)
		sortOfElement[c] = -1;
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (int elem : directElements[s1]){
			if (sortOfElement[elem] != -1){
				std::cerr << "Sort is contained in two types .. this cannot happen. Thus must be a bug. Exiting." << std::endl;
				exit(1);
			}
			sortOfElement[elem] = s1;
		}

	return std::make_tuple(parent,sortOfElement, replacedSorts);
} 


void topsortTypesCPDDL_dfs(int cur, std::vector<int> & parent,
						   std::vector<bool> & done, std::vector<int> & result){
	assert(cur != -2); // replaced sort
	if (cur == -1) return;
	if (done[cur]) return;
	done[cur] = true;
	topsortTypesCPDDL_dfs(parent[cur],parent,done,result);
	result.push_back(cur);
}


std::vector<int> topsortTypesCPDDL(std::vector<int> & parent){
	std::vector<bool> done (parent.size());
	for (size_t i = 0; i < done.size(); i++) done[i] = false;

	std::vector<int> result;
	for (size_t i = 0; i < done.size(); i++)
		if (!done[i] && parent[i] != -2)
			topsortTypesCPDDL_dfs(i,parent,done,result);

	return result;
}


void cpddl_add_object_of_sort(pddl_t * pddl, const std::string & name, int type){
	pddl_obj_t * obj = pddlObjsAdd(&pddl->obj,name.c_str());
	obj->type = type;
	obj->is_constant = true;
	obj->is_private = 0;
	obj->owner = PDDL_OBJ_ID_UNDEF;
	obj->is_agent = 0;
}

pddl_cond_t* cpddl_create_atom(const PredicateWithArguments & lit, bool positive){
	pddl_cond_atom_t * atom = condAtomNew();
	atom->pred = lit.predicateNo + 1; // +1 for equals
	atom->arg_size = lit.arguments.size();
	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
	atom->neg = !positive;
	for (size_t i = 0; i < lit.arguments.size(); i++){
		atom->arg[i].param = lit.arguments[i];
		atom->arg[i].obj = PDDL_OBJ_ID_UNDEF;
	}
	return &atom->cls;
}

void cpddl_add_atom_to_conjunction(const PredicateWithArguments & lit, bool positive, pddl_cond_part_t * conj){
	condPartAdd(conj,cpddl_create_atom(lit,positive));
}

void cpddl_add_fact_to_conjunction(const Fact & f, pddl_cond_part_t * conj, const Domain & domain, pddl_t * pddl){
	pddl_cond_atom_t * atom = condAtomNew();
	atom->pred = f.predicateNo + 1; // +1 for equals
	atom->arg_size = f.arguments.size();
	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
	atom->neg = false;
	for (size_t i = 0; i < f.arguments.size(); i++){
		atom->arg[i].param = -1;
		atom->arg[i].obj = pddlObjsGet(&pddl->obj, domain.constants[f.arguments[i]].c_str()); 
	}
	condPartAdd(conj,&atom->cls);
}

std::tuple<pddl_lifted_mgroups_t,pddl_t*,std::vector<int>> cpddl_compute_FAM_mutexes(const Domain & domain, const Problem & problem, grounding_configuration & config){
	// create representation of the domain/problem
	pddl_t * pddl = new pddl_t;
	bzero(pddl,sizeof(pddl_t));
	std::string name = "dom";
	pddl->domain_name = const_cast<char*>(name.c_str());
	std::string name2 = "prob";
	pddl->problem_name = const_cast<char*>(name2.c_str());
	pddl->require = PDDL_REQUIRE_TYPING + PDDL_REQUIRE_CONDITIONAL_EFF;
	
	// check if a super type already exists
	for (size_t s = 0; s <= domain.sorts.size(); s++){
		if (s == domain.sorts.size()){
			// add a super type _cpddl_object, which contains all constants
			Sort _cpddl_object;
			_cpddl_object.name = "_cpddl_object";
			for (size_t i = 0; i < domain.constants.size(); i++) _cpddl_object.members.insert(i);
			const_cast<Domain &>(domain).sorts.push_back(_cpddl_object);
			break;
		} else if (domain.sorts[s].members.size() == domain.constants.size()) break; // domain has object type;
	}


	// compute a local type hierarchy
	auto [typeParents,objectType,replacedTypes] = compute_local_type_hierarchy(domain,problem,config);
	
	// cpddl needs a root type named object
	pddlTypesAdd(&pddl->type,root_type_cppdl,-1);
	
	std::map<int,int> ourTypeIDToCPDDL;
	std::vector<int> cpddlTypesToOurs;
	ourTypeIDToCPDDL[-1] = 0;
	cpddlTypesToOurs.push_back(-1);
	for (int sort : topsortTypesCPDDL(typeParents)){
		int newID = ourTypeIDToCPDDL.size();
		ourTypeIDToCPDDL[sort] = newID;
		cpddlTypesToOurs.push_back(sort);
		DEBUG(std::cout << "Adding sort " << sort << " (\"" << domain.sorts[sort].name << "\")" << std::endl);
		DEBUG(std::cout << "\tParent is " << typeParents[sort] << std::endl);
			// +1 is for the artificial root sort
		assert(typeParents[sort] != -2); // removed sorts
		pddlTypesAdd(&pddl->type,domain.sorts[sort].name.c_str(),ourTypeIDToCPDDL[typeParents[sort]]);
	}

	// add ids for replaced sorts
	for (auto [sort,replacement] : replacedTypes)
		ourTypeIDToCPDDL[sort] = ourTypeIDToCPDDL[replacement];

	
	bzero(&pddl->obj, sizeof(pddl->obj));
	pddl->obj.htable = borHTableNew(objHash, objEq, NULL);
	
	// add objects
	for (size_t o = 0; o < domain.constants.size(); o++)
		cpddl_add_object_of_sort(pddl,domain.constants[o], ourTypeIDToCPDDL[objectType[o]]);
	
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c
    for (int i = 0; i < pddl->obj.obj_size; ++i){
        pddlTypesAddObj(&pddl->type, i, pddl->obj.obj[i].type);
	}
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c
	
	// add equals predicate
/////////////////////////////////// COPIED FROM CPDDL/src/pred.c
    pddl->pred.eq_pred = -1;
    addEqPredicate(&pddl->pred);
/////////////////////////////////// COPIED FROM CPDDL/src/pred.c


	for (const Predicate & pred : domain.predicates){
		pddl_pred_t * p = pddlPredsAdd(&pddl->pred);
		p->name = BOR_STRDUP(pred.name.c_str());
		p->param_size = pred.argumentSorts.size();
    	p->param = BOR_REALLOC_ARR(p->param, int, p->param_size);
        for (size_t i = 0; i < pred.argumentSorts.size(); i++)
			p->param[i] = ourTypeIDToCPDDL[pred.argumentSorts[i]];
	}

	// add dummy predicate to avoid pruning
	pddl_pred_t * dumm_goal_predicate = pddlPredsAdd(&pddl->pred);
	dumm_goal_predicate->name = BOR_STRDUP("dummy-goal");
	dumm_goal_predicate->param_size = 0;
	dumm_goal_predicate->param = BOR_REALLOC_ARR(dumm_goal_predicate->param, int, dumm_goal_predicate->param_size);

	// add actions to the model
	for (size_t tid = 0; tid < domain.nPrimitiveTasks; tid++){
		const Task & t = domain.tasks[tid];
    	pddl_action_t *a;
    	a = pddlActionsAddEmpty(&pddl->action);
		a->name = BOR_STRDUP(t.name.c_str());

		int varidx = 0;
		for (const int & parameter : t.variableSorts){
			pddl_param_t * p = pddlParamsAdd(&(a->param));
			std::string paramName = "?var" + std::to_string(varidx++);
			p->name = BOR_STRDUP(paramName.c_str());
			p->type = ourTypeIDToCPDDL[parameter];
			p->is_agent = 0;
		}

		if (t.preconditions.size() + t.variableConstraints.size() == 0){
			a->pre = pddlCondNewEmptyAnd();
		} else {
			// add preconditions
			pddl_cond_part_t * pre_conj = condPartNew(PDDL_COND_AND);
			for (const PredicateWithArguments & pre : t.preconditions)
				cpddl_add_atom_to_conjunction(pre, true, pre_conj); // true = positive
			
			// add the variable constraints
			for (const VariableConstraint & vc : t.variableConstraints){
				PredicateWithArguments equalsLiteral;
				equalsLiteral.predicateNo = -1; // equals	
				equalsLiteral.arguments.clear();
				equalsLiteral.arguments.push_back(vc.var1);
				equalsLiteral.arguments.push_back(vc.var2);
				cpddl_add_atom_to_conjunction(equalsLiteral, vc.type == VariableConstraint::Type::EQUAL, pre_conj);
			}
			
			
			a->pre = &(pre_conj->cls);
			pddlCondSetPredRead(a->pre, &pddl->pred);
		}



		// effects
		pddl_cond_part_t * eff_conj = condPartNew(PDDL_COND_AND);
		PredicateWithArguments goalLiteral;
		goalLiteral.predicateNo = domain.predicates.size();	
		goalLiteral.arguments.clear();
		cpddl_add_atom_to_conjunction(goalLiteral, true, eff_conj);

		// unconditional add and delete effects
		for (auto & add : t.effectsAdd)
			cpddl_add_atom_to_conjunction(add, true, eff_conj);
		
		for (auto & del : t.effectsDel)
			cpddl_add_atom_to_conjunction(del, false, eff_conj);
		
		
		// copy conditional effects into data structure to handle them uniformly
		std::vector<std::pair<bool,std::pair<std::vector<PredicateWithArguments>, PredicateWithArguments>>> cond_eff;
		for (auto & add : t.conditionalAdd)
			cond_eff.push_back(std::make_pair(true,add));
		for (auto & del : t.conditionalDel)
			cond_eff.push_back(std::make_pair(false,del));

		for (auto & eff : cond_eff){
			pddl_cond_when_t * w = condNew(pddl_cond_when_t, PDDL_COND_WHEN);

			// build precondition of CE
			pddl_cond_part_t * pre_conj = condPartNew(PDDL_COND_AND);
			for (const PredicateWithArguments & pre : eff.second.first)
				cpddl_add_atom_to_conjunction(pre, true, pre_conj);
			w->pre = &pre_conj->cls;

			// build conditional effect
			w->eff = cpddl_create_atom(eff.second.second,eff.first);
			condPartAdd(eff_conj,&w->cls);
		}

		a->eff = &(eff_conj->cls);
		pddlCondSetPredReadWriteEff(a->eff, &pddl->pred);
	}





	//// PROBLEM DEFINITION

	// init
	pddl->init = condPartNew(PDDL_COND_AND);
	for (const Fact & f : problem.init)
		cpddl_add_fact_to_conjunction(f,pddl->init, domain, pddl);

	
	// set all atoms in into to be in init (else normalisation will not work)	
/////////////////////////////////// COPIED FROM CPDDL/src/pddl.c
	{
		pddl_cond_const_it_atom_t it;
    	const pddl_cond_atom_t *atom;
	    PDDL_COND_FOR_EACH_ATOM(&pddl->init->cls, &it, atom)
        	pddl->pred.pred[atom->pred].in_init = 1;
	}
/////////////////////////////////// COPIED FROM CPDDL/src/pddl.c


// goal
	pddl_cond_part_t * goal = condPartNew(PDDL_COND_AND);
	// artificial goal predicate
	Fact goalFact;
	goalFact.predicateNo = domain.predicates.size();
	goalFact.arguments.clear();
	cpddl_add_fact_to_conjunction(goalFact, goal, domain, pddl);

	for (const Fact & f : problem.goal)
		cpddl_add_fact_to_conjunction(f, goal, domain, pddl);
	pddl->goal = &(goal->cls);

	pddlTypesBuildObjTypeMap(&pddl->type, pddl->obj.obj_size);

	// Normalize pddl, i.e. remove stuff and so on
	pddlNormalize(pddl);

	DEBUG(pddlPrintPDDLDomain(pddl,stdout));
	DEBUG(pddlPrintPDDLProblem(pddl,stdout));


	//////////////////// Mutex computation
	pddl_lifted_mgroups_infer_limits_t limits = PDDL_LIFTED_MGROUPS_INFER_LIMITS_INIT;
	limits.max_candidates = 10000;
	limits.max_mgroups = 10000;
	pddl_lifted_mgroups_t lifted_mgroups;
	pddlLiftedMGroupsInit(&lifted_mgroups);
	bor_err_t err = BOR_ERR_INIT;
	if (!config.quietMode)
		std::cout << "Computing Lifted FAM-Groups [Fiser, AAAI 2020]" << std::endl;
	pddlLiftedMGroupsInferFAMGroups(pddl, &limits, &lifted_mgroups, &err);

	if (!config.quietMode)
		std::cout << "Found " << lifted_mgroups.mgroup_size << " Lifted FAM-Groups" << std::endl;

	DEBUG(for (int li = 0; li < lifted_mgroups.mgroup_size; ++li){
        fprintf(stdout, "M:%d: ", li);
        pddlLiftedMGroupPrint(pddl, lifted_mgroups.mgroup + li, stdout);
    });


	return std::make_tuple(lifted_mgroups,pddl,cpddlTypesToOurs);
}


bool is_mutex_group_contained_in_assignement(pddl_lifted_mgroup_t * m1, pddl_lifted_mgroup_t *m2, std::vector<int> & m1VarTom2Var, std::vector<bool> & m2VarAssigned, pddl_t * pddl, int pos = 0){

	if (pos == m1VarTom2Var.size()){
		DEBUG(std::cout << "Assignment:";
		for (size_t m1V = 0; m1V < m1VarTom2Var.size(); m1V++)
			std::cout << " " << m1V << " -> " << m1VarTom2Var[m1V];
		std::cout << std::endl;);


		// we have to search for every condition in m1 a mirror partner in m2
		for (size_t m1i = 0; m1i < m1->cond.size; m1i++){
			bool matchFound = false;
			for (size_t m2i = 0; !matchFound && m2i < m2->cond.size; m2i++){
				// get both atoms
				pddl_cond_atom_t *a1 = PDDL_COND_CAST(m1->cond.cond[m1i], atom);
				pddl_cond_atom_t *a2 = PDDL_COND_CAST(m2->cond.cond[m2i], atom);

				// must have the same predicate
				if (a1->pred != a2->pred) continue;

				bool paramsMatch = true;
				// iterate through the parameters
				for (size_t param = 0; paramsMatch && param < a1->arg_size; param++){
					// get both parameters
					pddl_cond_atom_arg_t *p1 = a1->arg + param;
					pddl_cond_atom_arg_t *p2 = a2->arg + param;

					// cases
					if (p1->param < 0){
						// parameter p1 of a1 is a constant
						if (p2->param < 0) {
							// p2 is also a constant
							if (p1->obj != p2->obj){
								paramsMatch = false;
								break;
							} // else ok
						} else {
							// p2 is a variable
							const pddl_param_t *v2 = m2->param.param + p2->param;
							//pddl_type_t * t2 = pddl->type.type[v2->type];
							if (!pddlTypesObjHasType(&(pddl->type), v2->type,
										p1->obj)){
								paramsMatch = false;
								break;
							} // else object is in type, so ok
						}
					} else {
						// super mutex cannot have a constant here
						if (p2->param < 0){
							paramsMatch = false;
							break;
						}
						
						// test whether the variable of m1 is mapped to the one of m2
						if (m1VarTom2Var[p1->param] != p2->param){
							paramsMatch = false;
							break;
						}

						// mapped to the same variable so ok.
					}
				}
				if (paramsMatch) {
					matchFound = true;
					DEBUG(std::cout << "Match for " << m1i << " is " << m2i << std::endl);
				}
			}

			if (! matchFound) {
				DEBUG(std::cout << "Conjunct " << m1i << " has no match " << std::endl);
				return false;
			}
		
		}
	
		// here we have found a match for every condition	
		DEBUG(std::cout << "Given m1 is a sub-mutex of m2." << std::endl);
		return true;
	}

	// iterate through all possible remaining variables
	for (size_t m2Var = 0; m2Var < m2VarAssigned.size(); m2Var++){
		if (m2VarAssigned[m2Var]) continue;
						
		const pddl_param_t *v1 = m1->param.param + pos;
		const pddl_param_t *v2 = m2->param.param + m2Var;

		// we cannot map a counted var to an uncounted one ...
		if (v1->is_counted_var && !v2->is_counted_var)
			continue;

		// situation is either (C,C), (V,V) or (V,C)
		// in any case now m2 is at least as strong if the types are subtypes of each other (i.e. v1->type \subseteq v2->type)
		if (v1->type != v2->type)
			if (!pddlTypesIsParent(&(pddl->type),v1->type,v2->type))
				continue;


		// try is
		m1VarTom2Var[pos] = m2Var;
		m2VarAssigned[m2Var] = true;
		if (is_mutex_group_contained_in_assignement(m1,m2,m1VarTom2Var,m2VarAssigned,pddl,pos+1))
			return true;
		m2VarAssigned[m2Var] = false;
	}


	return false;
}



// tests whether the mgroup m1 is fully contained in m2
bool is_mutex_group_contained_in(pddl_lifted_mgroup_t * m1, pddl_lifted_mgroup_t *m2, pddl_t * pddl){
	// if m1 has *more* parameters it cannot be a subset of m2
	if (m1->param.param_size > m2->param.param_size)
		return false;

	std::vector<int>  m1VarTom2Var  (m1->param.param_size);
	std::vector<bool> m2VarAssigned (m2->param.param_size);

	return is_mutex_group_contained_in_assignement(m1,m2,m1VarTom2Var,m2VarAssigned,pddl);
} 




std::vector<FAMGroup> compute_FAM_mutexes(const Domain & domain, const Problem & problem, grounding_configuration & config){
	// pddl_lifted_mgroups_t ; pddl_t*, map<int,int>
	auto [lifted_mgroups,pddl,cpddlTypesToOurs] = cpddl_compute_FAM_mutexes(domain,problem,config);


	std::vector<bool> pruned (lifted_mgroups.mgroup_size);
	for (int i = 0; i < lifted_mgroups.mgroup_size; ++i)
		for (int j = 0; j < lifted_mgroups.mgroup_size; ++j)
			if (i != j && !pruned[i] && !pruned[j]){
				DEBUG(std::cout << "Testing whether M" << i << " < M" << j << std::endl);

				if (is_mutex_group_contained_in(lifted_mgroups.mgroup + i, lifted_mgroups.mgroup + j, pddl)){
					DEBUG(std::cout << "Yes. So we prune m1." << std::endl);
					pruned[i] = true;
				}
			}

	DEBUG(
		std::cout << std::endl << std::endl << "FAM-Mutexes after reduction" << std::endl;
		for (int li = 0; li < lifted_mgroups.mgroup_size; ++li){
		if (pruned[li]) continue;
        fprintf(stdout, "M:%d: ", li);
        pddlLiftedMGroupPrint(pddl, lifted_mgroups.mgroup + li, stdout);
    });



	// convert CPDDL FAM mutexes into a representation of pandaPIgrounder
	std::vector<FAMGroup> groups;
	for (int li = 0; li < lifted_mgroups.mgroup_size; ++li){
		if (pruned[li]) continue;
		FAMGroup g;

		// translate parameters
		pddl_lifted_mgroup_t * m = lifted_mgroups.mgroup + li;
		for(size_t v = 0; v < m->param.param_size; v++){
			const pddl_param_t *cpddl_v = m->param.param + v;
			FAMVariable var;
			var.sort = cpddlTypesToOurs[cpddl_v->type];
			var.isCounted = cpddl_v->is_counted_var;

			if (var.isCounted) {
				g.vars_to_pos_in_separated_lists.push_back(g.counted_vars.size());
				g.counted_vars.push_back(v);
			} else {
				g.vars_to_pos_in_separated_lists.push_back(g.free_vars.size());
				g.free_vars.push_back(v);
			}
			
			g.vars.push_back(var);
		}

		// translate elements
		for (size_t mi = 0; mi < m->cond.size; mi++){
			FAMGroupLiteral l;
			pddl_cond_atom_t *a = PDDL_COND_CAST(m->cond.cond[mi], atom);
			l.predicateNo = a->pred - 1; // artificial sort
			// add parameters
			for (size_t param = 0;param < a->arg_size; param++){
				pddl_cond_atom_arg_t *p = a->arg + param;
				if (p->param < 0){
					// get the object
					l.args.push_back(p->obj);
					l.isConstant.push_back(true);	
				} else {
					l.args.push_back(p->param);
					l.isConstant.push_back(false);	
				}
			}

			g.literals.push_back(l);
		}
		groups.push_back(g);
	}

	DEBUG(
		std::cout << "FAM Groups in pandaPI's format." << std::endl;
		for (FAMGroup & g : groups){
			std::cout << "Group:" << std::endl;
			for (size_t vid = 0; vid < g.vars.size(); vid++)
				if (!g.vars[vid].isCounted)
					std::cout << " V" << vid << ":" << domain.sorts[g.vars[vid].sort].name;
			for (size_t vid = 0; vid < g.vars.size(); vid++)
				if (g.vars[vid].isCounted)
					std::cout << " C" << vid << ":" << domain.sorts[g.vars[vid].sort].name;

			std::cout << " :";
			for (FAMGroupLiteral & l : g.literals){
				std::cout << " (" << domain.predicates[l.predicateNo].name;
				for (size_t a = 0; a < l.args.size(); a++){
					if (l.isConstant[a]) std::cout << " " << domain.constants[l.args[a]];
					else std::cout << " " << l.args[a];
				}
				
				std::cout << ")";
			}

			std::cout << std::endl;	
		}
	);
		
	return groups;
}
