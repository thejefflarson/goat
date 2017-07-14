#include <string>
#include "util.hh"

using namespace goat::util;
std::string alpha = "abcdefghijklmnopqrstuvwxyz";
std::string Namer::next() {
  if(last_ == 0){ last_++; return "a"; }
  uint32_t current = last_;
  std::string accum;
  while(current > 0) {
    uint8_t index = current % alpha.length();
    accum.push_back(alpha[index]);
    current /= alpha.length();
  }
  last_++;
  return accum;
}
