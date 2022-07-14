/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A hash function for Boolean.
 */

#ifndef CVC5__EXPECTED_H
#define CVC5__EXPECTED_H

namespace cvc5::internal {

template <class E>
class unexpected
{
  public:
  unexpected(const E& err)
  {
    new (&d_err) E(err);
  }

  const E& error() const {
    return d_err;
  }

  private:
  E d_err;
};

template <class T, class E>
class expected
{
 public:
  expected()
  {
    new (&d_val) T();
    d_hasValue = true;
  }

  expected(const T& t)
  {
    new (&d_val) T(t);
    d_hasValue = true;
  }

  expected(const unexpected<E>& e)
  {
    new (&d_err) E(e.error());
    d_hasValue = false;
  }

  ~expected()
  {
    if (d_hasValue)
    {
      d_val.~T();
    }
    else
    {
      d_err.~E();
    }
  }

  explicit operator bool() const {
    return d_hasValue;
  }

  T& operator*() {
    if (!d_hasValue) {
      throw d_err;
    }
    return d_val;
  }

  const T& operator*() const {
    if (!d_hasValue) {
      throw d_err;
    }
    return d_val;
  }

  T& value() {
    return **this;
  }

  const T& value() const {
    return **this;
  }

  const E& error() const {
    return d_err;
  }

 private:
  union
  {
    T d_val;
    E d_err;
  };

  bool d_hasValue;
};

}  // namespace cvc5::internal

#endif
