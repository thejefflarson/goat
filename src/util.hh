#ifndef SRC_UTIL_H_
#define SRC_UTIL_H_

#include <algorithm>
#include <memory>
#include <new>
#include <tuple>
#include <typeindex>
#include <type_traits>
#include <vector>

namespace goat {

namespace node {
class Visitor;
}

namespace util {
template <typename T>
bool compare_vector_pointers(const T &a, const T &b) {
  if (a->size() != b->size())
    return false;

  auto eq = [](const auto &a, const auto &b) {
    return *a == *b;
  };

  return std::equal(a->begin(), a->end(), b->begin(), eq);
}

template <typename T>
void list_accept(const T list, node::Visitor &v) {
  for(auto i : *list) {
    i->accept(v);
  }
}

// Simple variant class to help with rust style pattern
// matching, extremely limited on purpose. Inspiration
// drawn from mapbox variant
template <typename... Types>
struct variant_helper;

template <typename First, typename... Types>
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
      new (new_data) First(*reinterpret_cast<const First *>(old_data));
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

template <>
struct variant_helper<> {
  static void destroy(std::type_index t, void *data) {}
  static void copy(std::type_index t, const void *old_data, void *new_data) {}
  static void move(std::type_index t, void *old_data, void *new_data) {}
};

template <typename Function, typename Variant,
          typename Return, typename... Types>
struct variant_visitor;

template <typename Function, typename Variant, typename Return,
          typename First, typename... Types>
struct variant_visitor<Function, Variant, Return, First, Types...> {
  static Return visit(const Variant& variant, Function&& fn) {
    if(variant.template is<First>()) {
      return fn(variant.template get<First>());
    } else {
      return variant_visitor<Function, Variant, Return, Types...>::visit(
        variant, std::forward<Function>(fn)
      );
    }
  }
};

template <typename Function, typename Variant, typename Return, typename Type>
struct variant_visitor<Function, Variant, Return, Type> {
  static Return visit(const Variant& variant, Function&& fn) {
    return fn(variant.template get<Type>());
  }
};

struct equal {
  template <typename T>
  bool call(const T& lhs, const T& rhs) {
    return lhs == rhs;
  }
};

struct less {
  template <typename T>
  bool call(const T& lhs, const T& rhs) {
    return lhs < rhs;
  }
};

template <typename Variant, typename Compare>
class Comparer {
 public:
  explicit Comparer(const Variant& variant) :
    variant_(variant) {}
  Comparer& operator=(const Comparer&) = delete;

  template <typename T>
  bool operator()(T& other) {
    const T& value = variant_.template get<T>();
    return Compare().call(value, other);
  }

 private:
  Variant const& variant_;
};


// from https://stackoverflow.com/questions/17032310/how-to-make-a-variadic-is-same
template<typename T, typename... Rest>
struct is_any : std::false_type {};

template<typename T, typename First>
struct is_any<T, First> : std::is_same<T, First> {};

template<typename T, typename First, typename... Rest>
struct is_any<T, First, Rest...>
    : std::integral_constant<bool, std::is_same<T, First>::value ||
                             is_any<T, Rest...>::value> {};

template <typename... Types>
class Variant {
 public:
  Variant() : type_(typeid(first)) {
    new (&data_) first();
  };

  template<typename T,
           typename = std::enable_if_t<is_any<T, Types...>::value>>
  Variant(T &&t) : type_(typeid(T)) {
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
  const T& get() const {
    return *reinterpret_cast<const T*>(&data_);
  }

  Variant<Types...>&& operator=(Variant<Types...> &&other) {
    Variant<Types...> temp(std::move(other));
    move_assign(std::move(temp));
    return *this;
  }

  Variant<Types...>& operator=(const Variant<Types...> &other) {
    copy_assign(other);
    return *this;
  }

  template<typename T>
  Variant<Types...>& operator=(T &&other) {
    Variant<Types...> tmp(std::forward<T>(other));
    move_assign(std::move(tmp));
    return *this;
  }

  template<typename T>
  Variant<Types...>& operator=(T &other) {
    Variant<Types...> tmp(other);
    copy_assign(std::move(tmp));
    return *this;
  }

  bool operator==(const Variant<Types...> &other) const {
     if(type_ != other.type_) {
       return false;
     } else {
        return variant_visitor<Comparer<Variant, equal>,
                               Variant<Types...>, bool,
                               Types...>::visit(
                                 other, Comparer<Variant, equal>(*this)
                               );
     }
  }

  bool operator!=(const Variant<Types...> &other) const {
    return !(*this == other);
  }

  bool operator<(const Variant<Types...> &other) const {
    if(type_ < other.type_) {
      return true;
    } else {
      return variant_visitor<Comparer<Variant, less>,
                             Variant<Types...>, bool,
                             Types...>::visit(
                               other, Comparer<Variant, less>(*this)
                             );
    }
  }

  ~Variant() {
    helper_t::destroy(type_, &data_);
  }
 private:
  void move_assign(const Variant<Types...> &&other) {
    helper_t::destroy(type_, &data_);
    helper_t::move(other.type_, &other.data_, &data_);
    type_ = other.type_;
  }

  void copy_assign(const Variant<Types...> &other) {
    helper_t::destroy(type_, &data_);
    helper_t::copy(other.type_, &other.data_, &data_);
    type_ = other.type_;
  }

  using types = std::tuple<Types...>;
  using first = typename std::tuple_element<0, types>::type;
  using data_t = typename std::aligned_union<1, Types...>::type;
  using helper_t = variant_helper<Types...>;
  data_t data_;
  std::type_index type_;
};
}
}
#endif
