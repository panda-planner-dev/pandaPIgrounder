#ifndef PARSER_H_INCLUDED
#define PARSER_H_INCLUDED

/**
 * @defgroup parser Input Data Parser
 * @brief Contains functions for parsing input data.
 *
 * @{
 */

#include <fstream>

#include "model.h"

/**
 * @brief Parse input from an input stream.
 *
 * @param[in] is The input stream to read from.
 * @param[out] output The Domain object to write to.
 * @return Returns true if successful, or false if there was an error while reading.
 */
bool readInput (std::istream & is, Domain & output, Problem & outputProblem);

/**
 * @}
 */

#endif
