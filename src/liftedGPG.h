#ifndef LGPG_H_INCLUDED
#define LGPG_H_INCLUDED

#include "model.h"
#include "grounding.h"

std::tuple<std::vector<Fact>, std::vector<GroundedTask>, std::vector<GroundedMethod>> run_lifted_HTN_GPG(const Domain & domain, const Problem & problem, grounding_configuration & config);

#endif
