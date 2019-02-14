#include <string>
#include <tuple>

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
