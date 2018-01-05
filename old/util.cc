#include <cstring>
#include <string>
#include "util.hh"

using namespace goat::util;
const char alpha[] = "abcdefghijklmnopqrstuvwxyz";
std::string Namer::next() {
  if(last_ == 0){ last_++; return "a"; }
  uint32_t current = last_;
  std::string accum;
  while(current > 0) {
    uint8_t index = current % strlen(alpha);
    accum.push_back(alpha[index]);
    current /= strlen(alpha);
  }
  last_++;
  return accum;
}
