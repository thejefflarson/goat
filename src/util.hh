#ifndef SRC_UTIL_H_
#define SRC_UTIL_H_

#include <memory>
#include <typeindex>
#include <type_traits>
#include <vector>

namespace goat {

namespace node {
class Visitor;
}

namespace util {
template<typename T>
bool compare_vector_pointers(const T &a, const T &b) {
  if (a->size() != b->size())
    return false;

  auto eq = [](const auto &a, const auto &b) {
    return *a == *b;
  };

  return std::equal(a->begin(), a->end(), b->begin(), eq);
}

template<typename T>
void list_accept(const T list, node::Visitor &v) {
  for(auto i : *list) {
    i->accept(v);
  }
}

// Simple variant class to help with rust style pattern
// matching, extremely limited on purpose. Inspiration
// drawn from mapbox variant
template<typename... Types>
struct variant_helper;

template<typename First, typename... Types>
struct variant_helper<First, Types...> {
  static void destroy(std::type_index t, void *data) {
    if(t == std::type_index(typeid(First))) {
      reinterpret_cast<First *>(data)->~First();
    } else {
      variant_helper<Types...>::destroy(t, data);
    }
  }

  static void copy(std::type_index t, const void *old_data, void *new_data) {
    if(t == std::type_index(typeid(First))) {
      new (new_data) First(*reinterpret_cast<First *>(old_data));
    } else {
       variant_helper<Types...>::copy(t, old_data, new_data);
    }
  }

  static void move(std::type_index t, void *old_data, void *new_data) {
    if(t == std::type_index(typeid(First))) {
      new (new_data) First(std::move(*reinterpret_cast<First *>(old_data)));
    } else {
       variant_helper<Types...>::move(t, old_data, new_data);
    }
  }
};

template<>
struct variant_helper<> {
  static void destroy(std::type_index t, void *data) {}
  static void copy(std::type_index t, const void *old_data, void *new_data) {}
  static void move(std::type_index t, void *old_data, void *new_data) {}
};


template<typename... Types>
class Variant {
public:
  Variant() = delete;
  // WARNING: no check if an invalid type is here.
  template<typename T>
  Variant(T& t) : type_(typeid(T)) {
    new (&data_) T(std::forward<T>(t));
  }

  Variant(const Variant<Types...> &old) : type_(old.type_) {
    helper_t::copy(type_, &old.data_, &data_);
  }

  Variant(Variant<Types...> &&old) : type_(old.type_) {
    helper_t::move(type_, &old.data_, &data_);
  }

  template<typename T>
  bool is() const {
    return type_ == std::type_index(typeid(T));
  }

  template<typename T>
  T& get() {
    return *reinterpret_cast<T*>(data_);
  }

  template<typename T>
  Variant<Types...>& operator=(T &other) {
    Variant<Types...> tmp(other);
    move_assign(std::move(tmp));
    return *this;
  }

  ~Variant() {
    helper_t::destroy(type_, &data_);
  }
private:
  void move_assign(Variant<Types...> &&other) {
    helper_t::destroy(type_, &data_);
    helper_t::move(other.type_, &other.data_, &data_);
    type_ = other.type_;
  }

  void copy_assign(Variant<Types...> const &other) {
    helper_t::destroy(type_, &data_);
    helper_t::copy(other.type_, &other.data_, &data_);
    type_ = other.type_;
  }

  using data_t = typename std::aligned_union<1, Types...>::type;
  using helper_t = variant_helper<Types...>;
  data_t data_;
  std::type_index type_;
};
}
}
#endif
