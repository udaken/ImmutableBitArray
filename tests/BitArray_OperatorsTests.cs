// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;

namespace Collections.Immutable.Tests
{
    public static class BitArray_OperatorsTests
    {
        private const int BitsPerByte = 8;
        private const int BitsPerInt32 = 32;

        public static IEnumerable<object[]> Not_Operator_Data()
        {
            foreach (int size in new[] { 0, 1, BitsPerByte, BitsPerByte * 2, BitsPerInt32, BitsPerInt32 * 2, BitsPerInt32 * 3, BitsPerInt32 * 4, BitsPerInt32 * 5, BitsPerInt32 * 6, BitsPerInt32 * 7, BitsPerInt32 * 8, BitsPerInt32 * 8 + BitsPerInt32 - 1, short.MaxValue })
            {
                yield return new object[] { Enumerable.Repeat(true, size).ToArray() };
                yield return new object[] { Enumerable.Repeat(false, size).ToArray() };
                yield return new object[] { Enumerable.Range(0, size).Select(i => i % 2 == 1).ToArray() };
            }
        }

        [Theory]
        [MemberData(nameof(Not_Operator_Data))]
        public static void Not(bool[] data)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.From(data);

            ImmutableBitArray bitArrayNot = bitArray.Not();
            Assert.Equal(bitArray.Length, bitArrayNot.Length);
            for (int i = 0; i < bitArray.Length; i++)
            {
                Assert.Equal(!data[i], bitArrayNot[i]);
            }
        }

        public static IEnumerable<object[]> And_Operator_Data()
        {
            yield return new object[] { new bool[0], new bool[0], new bool[0] };
            foreach (int size in new[] { 1, BitsPerByte, BitsPerByte * 2, BitsPerInt32, BitsPerInt32 * 2, BitsPerInt32 * 3, BitsPerInt32 * 4, BitsPerInt32 * 5, BitsPerInt32 * 6, BitsPerInt32 * 7, BitsPerInt32 * 8, BitsPerInt32 * 8 + BitsPerInt32 - 1, short.MaxValue })
            {
                bool[] allTrue = Enumerable.Repeat(true, size).ToArray();
                bool[] allFalse = Enumerable.Repeat(false, size).ToArray();
                bool[] alternating = Enumerable.Range(0, size).Select(i => i % 2 == 1).ToArray();
                yield return new object[] { allTrue, allTrue, allTrue };
                yield return new object[] { allTrue, allFalse, allFalse };
                yield return new object[] { allFalse, allTrue, allFalse };
                yield return new object[] { allFalse, allFalse, allFalse };
                yield return new object[] { allTrue, alternating, alternating };
                yield return new object[] { alternating, allTrue, alternating };
                yield return new object[] { allFalse, alternating, allFalse };
                yield return new object[] { alternating, allFalse, allFalse };
            }
        }

        [Theory]
        [MemberData(nameof(And_Operator_Data))]
        public static void And_Operator(bool[] l, bool[] r, bool[] expected)
        {
            ImmutableBitArray left = ImmutableBitArray.From(l);
            ImmutableBitArray right = ImmutableBitArray.From(r);

            ImmutableBitArray actual = left.And(right);
            Assert.Equal(actual.Length, expected.Length);

            for (int i = 0; i < expected.Length; i++)
            {
                Assert.Equal(expected[i], actual[i]);
            }
        }

        public static IEnumerable<object[]> Or_Operator_Data()
        {
            yield return new object[] { new bool[0], new bool[0], new bool[0] };
            foreach (int size in new[] { 1, BitsPerByte, BitsPerByte * 2, BitsPerInt32, BitsPerInt32 * 2, BitsPerInt32 * 3, BitsPerInt32 * 4, BitsPerInt32 * 5, BitsPerInt32 * 6, BitsPerInt32 * 7, BitsPerInt32 * 8, BitsPerInt32 * 8 + BitsPerInt32 - 1, short.MaxValue })
            {
                bool[] allTrue = Enumerable.Repeat(true, size).ToArray();
                bool[] allFalse = Enumerable.Repeat(false, size).ToArray();
                bool[] alternating = Enumerable.Range(0, size).Select(i => i % 2 == 1).ToArray();
                yield return new object[] { allTrue, allTrue, allTrue };
                yield return new object[] { allTrue, allFalse, allTrue };
                yield return new object[] { allFalse, allTrue, allTrue };
                yield return new object[] { allFalse, allFalse, allFalse };
                yield return new object[] { allTrue, alternating, allTrue };
                yield return new object[] { alternating, allTrue, allTrue };
                yield return new object[] { allFalse, alternating, alternating };
                yield return new object[] { alternating, allFalse, alternating };
            }
        }

        [Theory]
        [MemberData(nameof(Or_Operator_Data))]
        public static void Or_Operator(bool[] l, bool[] r, bool[] expected)
        {
            ImmutableBitArray left = ImmutableBitArray.From(l);
            ImmutableBitArray right = ImmutableBitArray.From(r);

            ImmutableBitArray actual = left.Or(right);
            Assert.Equal(actual.Length, expected.Length);

            for (int i = 0; i < expected.Length; i++)
            {
                Assert.Equal(expected[i], actual[i]);
            }
        }

        public static IEnumerable<object[]> Xor_Operator_Data()
        {
            yield return new object[] { new bool[0], new bool[0], new bool[0] };
            foreach (int size in new[] { 1, BitsPerByte, BitsPerByte * 2, BitsPerInt32, BitsPerInt32 * 2, BitsPerInt32 * 3, BitsPerInt32 * 4, BitsPerInt32 * 5, BitsPerInt32 * 6, BitsPerInt32 * 7, BitsPerInt32 * 8, BitsPerInt32 * 8 + BitsPerInt32 - 1, short.MaxValue })
            {
                bool[] allTrue = Enumerable.Repeat(true, size).ToArray();
                bool[] allFalse = Enumerable.Repeat(false, size).ToArray();
                bool[] alternating = Enumerable.Range(0, size).Select(i => i % 2 == 1).ToArray();
                bool[] inverse = Enumerable.Range(0, size).Select(i => i % 2 == 0).ToArray();
                yield return new object[] { allTrue, allTrue, allFalse };
                yield return new object[] { allTrue, allFalse, allTrue };
                yield return new object[] { allFalse, allTrue, allTrue };
                yield return new object[] { allFalse, allFalse, allFalse };
                yield return new object[] { allTrue, alternating, inverse };
                yield return new object[] { alternating, allTrue, inverse };
                yield return new object[] { allFalse, alternating, alternating };
                yield return new object[] { alternating, allFalse, alternating };
                yield return new object[] { alternating, inverse, allTrue };
                yield return new object[] { inverse, alternating, allTrue };
            }
        }

        [Theory]
        [MemberData(nameof(Xor_Operator_Data))]
        public static void Xor_Operator(bool[] l, bool[] r, bool[] expected)
        {
            ImmutableBitArray left = ImmutableBitArray.From(l);
            ImmutableBitArray right = ImmutableBitArray.From(r);

            ImmutableBitArray actual = left.Xor(right);
            Assert.Equal(actual.Length, expected.Length);

            for (int i = 0; i < expected.Length; i++)
            {
                Assert.Equal(expected[i], actual[i]);
            }
        }

        [Fact]
        public static void And_Invalid()
        {
            ImmutableBitArray bitArray1 = ImmutableBitArray.Create(11, false);
            ImmutableBitArray bitArray2 = ImmutableBitArray.Create(6, false);

            // Different lengths
            Assert.Throws<ArgumentException>(null, () => bitArray1.And(bitArray2));
            Assert.Throws<ArgumentException>(null, () => bitArray2.And(bitArray1));

            Assert.Throws<ArgumentException>(null, () => bitArray1.And(default));
        }

        [Fact]
        public static void Or_Invalid()
        {
            ImmutableBitArray bitArray1 = ImmutableBitArray.Create(11, false);
            ImmutableBitArray bitArray2 = ImmutableBitArray.Create(6, false);

            // Different lengths
            Assert.Throws<ArgumentException>(null, () => bitArray1.Or(bitArray2));
            Assert.Throws<ArgumentException>(null, () => bitArray2.Or(bitArray1));

            Assert.Throws<ArgumentException>(null, () => bitArray1.Or(default));
        }

        [Fact]
        public static void Xor_Invalid()
        {
            ImmutableBitArray bitArray1 = ImmutableBitArray.Create(11, false);
            ImmutableBitArray bitArray2 = ImmutableBitArray.Create(6, false);

            // Different lengths
            Assert.Throws<ArgumentException>(null, () => bitArray1.Xor(bitArray2));
            Assert.Throws<ArgumentException>(null, () => bitArray2.Xor(bitArray1));

            Assert.Throws<ArgumentException>(null, () => bitArray1.Xor(default));
        }

        public static IEnumerable<object[]> Resize_TestData()
        {
            yield return new object[] { ImmutableBitArray.Create(32), ImmutableBitArray.Create(64), 32, 32 };
            yield return new object[] { ImmutableBitArray.Create(32), ImmutableBitArray.Create(64), 64, 64 };
            yield return new object[] { ImmutableBitArray.Create(64), ImmutableBitArray.Create(32), 32, 32 };
            yield return new object[] { ImmutableBitArray.Create(64), ImmutableBitArray.Create(32), 64, 64 };
            yield return new object[] { ImmutableBitArray.Create(288), ImmutableBitArray.Create(32), 288, 288 };
            yield return new object[] { ImmutableBitArray.Create(288), ImmutableBitArray.Create(32), 32, 32 };
            yield return new object[] { ImmutableBitArray.Create(32), ImmutableBitArray.Create(288), 288, 288 };
            yield return new object[] { ImmutableBitArray.Create(32), ImmutableBitArray.Create(288), 32, 32 };
            yield return new object[] { ImmutableBitArray.Create(1), ImmutableBitArray.Create(9), 9, 9 };
            yield return new object[] { ImmutableBitArray.Create(1), ImmutableBitArray.Create(9), 1, 1 };
            yield return new object[] { ImmutableBitArray.Create(9), ImmutableBitArray.Create(1), 9, 9 };
            yield return new object[] { ImmutableBitArray.Create(9), ImmutableBitArray.Create(1), 1, 1 };
            yield return new object[] { ImmutableBitArray.Create(287), ImmutableBitArray.Create(32), 32, 32 };
            yield return new object[] { ImmutableBitArray.Create(287), ImmutableBitArray.Create(32), 287, 287 };
            yield return new object[] { ImmutableBitArray.Create(32), ImmutableBitArray.Create(287), 32, 32 };
            yield return new object[] { ImmutableBitArray.Create(32), ImmutableBitArray.Create(287), 287, 287 };
            yield return new object[] { ImmutableBitArray.Create(289), ImmutableBitArray.Create(32), 289, 289 };
            yield return new object[] { ImmutableBitArray.Create(289), ImmutableBitArray.Create(32), 32, 32 };
            yield return new object[] { ImmutableBitArray.Create(32), ImmutableBitArray.Create(289), 289, 289 };
            yield return new object[] { ImmutableBitArray.Create(32), ImmutableBitArray.Create(289), 32, 32 };
        }

        [Theory]
        [MemberData(nameof(Resize_TestData))]
        public static void And_With_Resize(ImmutableBitArray left, ImmutableBitArray right, int newLeftLength, int newRightLength)
        {

            left.Resize(newLeftLength).And(right.Resize(newRightLength));
        }

        [Theory]
        [MemberData(nameof(Resize_TestData))]
        public static void Or_With_Resize(ImmutableBitArray left, ImmutableBitArray right, int newLeftLength, int newRightLength)
        {
            left.Resize(newLeftLength).Or(right.Resize(newRightLength));
        }

        [Theory]
        [MemberData(nameof(Resize_TestData))]
        public static void Xor_With_Resize(ImmutableBitArray left, ImmutableBitArray right, int newLeftLength, int newRightLength)
        {
            _ = left.Resize(newLeftLength).Xor(right.Resize(newRightLength));
        }

        #region Shift Tests

        public static IEnumerable<object[]> Shift_Data()
        {
            foreach (int size in new[] { 0, 1, BitsPerInt32 / 2, BitsPerInt32, BitsPerInt32 + 1, 2 * BitsPerInt32, 2 * BitsPerInt32 + 1 })
            {
                foreach (int shift in new[] { 0, 1, size / 2, size - 1, size }.Where(s => s >= 0).Distinct())
                {
                    yield return new object[] { size, new int[] { /* deliberately empty */ }, shift };
                    yield return new object[] { size, Enumerable.Range(0, size), shift };

                    if (size > 1)
                    {
                        foreach (int position in new[] { 0, size / 2, size - 1 })
                        {
                            yield return new object[] { size, new[] { position }, shift };
                        }
                        yield return new object[] { size, new[] { 0, size / 2, size - 1 }, shift };
                    }
                }
            }
        }

        [Theory]
        [MemberData(nameof(Shift_Data))]
        public static void RightShift(int length, IEnumerable<int> set, int shift)
        {
            ImmutableBitArray ba = ImmutableBitArray.From(GetBoolArray(length, set));
            bool[] expected = GetBoolArray(length, set.Select(i => i - shift).Where(i => i >= 0));

            ImmutableBitArray returned = ba.RightShift(shift);

            int index = 0;
            Assert.All(returned.Cast<bool>(), bit => Assert.Equal(expected[index++], bit));
        }

        [Theory]
        [MemberData(nameof(Shift_Data))]
        public static void LeftShift(int length, IEnumerable<int> set, int shift)
        {
            ImmutableBitArray ba = ImmutableBitArray.From(GetBoolArray(length, set));
            bool[] expected = GetBoolArray(length, set.Select(i => i + shift).Where(i => i < length));

            ImmutableBitArray returned = ba.LeftShift(shift);

            int index = 0;
            Assert.All(returned.Cast<bool>(), bit => Assert.Equal(expected[index++], bit));
        }

        private static bool[] GetBoolArray(int length, IEnumerable<int> set)
        {
            bool[] b = new bool[length];
            foreach (int position in set)
            {
                b[position] = true;
            }
            return b;
        }

        [Fact]
        public static void LeftShift_NegativeCount_ThrowsArgumentOutOfRangeException()
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(1);
            Assert.Throws<ArgumentOutOfRangeException>("count", () => bitArray.LeftShift(-1));
        }


        public static IEnumerable<object[]> RightShift_Hidden_Data()
        {
            yield return new object[] { "Constructor", Unset_Visible_Bits(ImmutableBitArray.Create(BitsPerInt32 / 2, true)) };
            yield return new object[] { "Not", Unset_Visible_Bits(ImmutableBitArray.Create(BitsPerInt32 / 2, false).Not()) };
            ImmutableBitArray setAll = ImmutableBitArray.Create(BitsPerInt32 / 2, true);
            yield return new object[] { "SetAll", Unset_Visible_Bits(setAll) };
            ImmutableBitArray lengthShort = ImmutableBitArray.Create(BitsPerInt32, true);
            lengthShort = lengthShort.Resize(BitsPerInt32 / 2);
            yield return new object[] { "Length-Short", Unset_Visible_Bits(lengthShort) };
            ImmutableBitArray lengthLong = ImmutableBitArray.Create(2 * BitsPerInt32, true);
            lengthLong = lengthLong.Resize(BitsPerInt32);
            yield return new object[] { "Length-Long", Unset_Visible_Bits(lengthLong) };
            ImmutableBitArray leftShift = ImmutableBitArray.Create(BitsPerInt32 / 2);
            for (int i = 0; i < leftShift.Length; i++)
            {
                leftShift = leftShift.Set(i, true);
            }

            yield return new object[] { "LeftShift", leftShift.LeftShift(BitsPerInt32 / 2) };
        }

        private static ImmutableBitArray Unset_Visible_Bits(ImmutableBitArray ba)
        {
            for (int i = 0; i < ba.Length; i++)
            {
                ba = ba.Set(i, false);
            }

            return ba;
        }

        [Theory]
        [MemberData(nameof(RightShift_Hidden_Data))]
        public static void RightShift_Hidden(string label, ImmutableBitArray bits)
        {
            _ = label;

            Assert.All(bits.Cast<bool>(), bit => Assert.False(bit));
            bits.RightShift(1);
            Assert.All(bits.Cast<bool>(), bit => Assert.False(bit));
        }

        [Fact]
        public static void RightShift_NegativeCount_ThrowsArgumentOutOfRangeException()
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(1);
            Assert.Throws<ArgumentOutOfRangeException>("count", () => bitArray.RightShift(-1));
        }

        #endregion
    }
}
