/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::internal::expected.
 */

#include <gtest/gtest.h>
#include <string>

#include "test.h"
#include "util/expected.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackExpected : public TestInternal
{
};

TEST_F(TestUtilBlackExpected, defaultConstructor)
{
    expected<uint32_t, std::string> x;
    ASSERT_TRUE(x);
}

TEST_F(TestUtilBlackExpected, implicitConversion) {
    expected<uint32_t, std::string> x = 42;
    ASSERT_TRUE(x);
    ASSERT_EQ(*x, 42);
    ASSERT_EQ(x.value(), 42);
}

TEST_F(TestUtilBlackExpected, unexpectedConstructor) {
  const char* errMsg = "foo";
    expected<uint32_t, std::string> x = unexpected<std::string>(errMsg);
    ASSERT_FALSE(x);
    ASSERT_EQ(x.error(), errMsg);
}

}  // namespace test
}  // namespace cvc5::internal
