#ifndef LGPG_H_INCLUDED
#define LGPG_H_INCLUDED

#include "model.h"
#include "grounding.h"
#include "givenPlan.h"

std::tuple<std::vector<Fact>, std::vector<GroundedTask>, std::vector<GroundedMethod>> run_lifted_HTN_GPG(const Domain & domain, const Problem & problem, grounding_configuration & config, given_plan_typing_information & given_typing);

#endif
