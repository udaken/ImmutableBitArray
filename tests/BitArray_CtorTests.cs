// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;

namespace Collections.Immutable.Tests
{
    public static class BitArray_CtorTests
    {
        private const int BitsPerByte = 8;
        private const int BitsPerInt32 = 32;

        [Theory]
        [InlineData(0)]
        [InlineData(1)]
        [InlineData(BitsPerByte)]
        [InlineData(BitsPerByte * 2)]
        [InlineData(BitsPerInt32)]
        [InlineData(BitsPerInt32 * 2)]
        [InlineData(200)]
        [InlineData(65551)]
        public static void Ctor_Int(int length)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(length);
            Assert.Equal(length, bitArray.Length);
            for (int i = 0; i < bitArray.Length; i++)
            {
                Assert.False(bitArray[i]);
                Assert.False(bitArray.Get(i));
            }
        }

        [Theory]
        [InlineData(0, true)]
        [InlineData(0, false)]
        [InlineData(1, true)]
        [InlineData(1, false)]
        [InlineData(BitsPerByte, true)]
        [InlineData(BitsPerByte, false)]
        [InlineData(BitsPerByte * 2, true)]
        [InlineData(BitsPerByte * 2, false)]
        [InlineData(BitsPerInt32, true)]
        [InlineData(BitsPerInt32, false)]
        [InlineData(BitsPerInt32 * 2, true)]
        [InlineData(BitsPerInt32 * 2, false)]
        [InlineData(200, true)]
        [InlineData(200, false)]
        [InlineData(65551, true)]
        [InlineData(65551, false)]
        public static void Ctor_Int_Bool(int length, bool defaultValue)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(length, defaultValue);
            Assert.Equal(length, bitArray.Length);
            for (int i = 0; i < bitArray.Length; i++)
            {
                Assert.Equal(defaultValue, bitArray[i]);
                Assert.Equal(defaultValue, bitArray.Get(i));
            }
        }

        [Fact]
        public static void Ctor_Int_Bool_ShouldNotLeaveDirtyBits()
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(33, true);
            bitArray = bitArray.RightShift(31);

            Assert.True(bitArray[0]);
            Assert.True(bitArray[1]);
            Assert.False(bitArray[2]);
        }

        [Fact]
        public static void Ctor_Int_NegativeLength_ThrowsArgumentOutOfRangeException()
        {
            Assert.Throws<ArgumentOutOfRangeException>("length", () => ImmutableBitArray.Create(-1));
            Assert.Throws<ArgumentOutOfRangeException>("length", () => ImmutableBitArray.Create(-1, false));
        }

        public static IEnumerable<object[]> Ctor_BoolArray_TestData()
        {
            Random rnd = new Random(0);

            yield return new object[] { new bool[0] };
            foreach (int size in new[] { 1, BitsPerByte, BitsPerByte * 2, BitsPerInt32, BitsPerInt32 * 2, BitsPerInt32 * 4, BitsPerInt32 * 8, BitsPerInt32 * 16 })
            {
                yield return new object[] { Enumerable.Repeat(true, size).ToArray() };
                yield return new object[] { Enumerable.Repeat(false, size).ToArray() };
                yield return new object[] { Enumerable.Range(0, size).Select(x => x % 2 == 0).ToArray() };

                bool[] random = new bool[size];
                for (int i = 0; i < random.Length; i++)
                {
                    random[i] = rnd.Next(0, 2) == 0;
                }

                yield return new object[] { random };
            }
        }

        [Theory]
        [MemberData(nameof(Ctor_BoolArray_TestData))]
        public static void Ctor_BoolArray(bool[] values)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.From(values);
            Assert.Equal(values.Length, bitArray.Length);
            for (int i = 0; i < bitArray.Length; i++)
            {
                Assert.Equal(values[i], bitArray[i]);
                Assert.Equal(values[i], bitArray.Get(i));
            }
        }

        public static IEnumerable<object[]> Ctor_BitArraySlim_TestData()
        {
            yield return new object[] { "bool[](empty)", ImmutableBitArray.From(new bool[0]) };
            yield return new object[] { "byte[](empty)", ImmutableBitArray.From(new byte[0]) };
            yield return new object[] { "int[](empty)", ImmutableBitArray.From(new int[0]) };

            foreach (int size in new[] { 1, BitsPerByte, BitsPerByte * 2, BitsPerInt32, BitsPerInt32 * 2 })
            {
                yield return new object[] { "length", ImmutableBitArray.Create(size) };
                yield return new object[] { "length|default(true)", ImmutableBitArray.Create(size, true) };
                yield return new object[] { "length|default(false)", ImmutableBitArray.Create(size, false) };
                yield return new object[] { "bool[](all)", ImmutableBitArray.From(Enumerable.Repeat(true, size).ToArray()) };
                yield return new object[] { "bool[](none)", ImmutableBitArray.From(Enumerable.Repeat(false, size).ToArray()) };
                yield return new object[] { "bool[](alternating)", ImmutableBitArray.From(Enumerable.Range(0, size).Select(x => x % 2 == 0).ToArray()) };
                if (size >= BitsPerByte)
                {
                    yield return new object[] { "byte[](all)", ImmutableBitArray.From(Enumerable.Repeat((byte)0xff, size / BitsPerByte).ToArray()) };
                    yield return new object[] { "byte[](none)", ImmutableBitArray.From(Enumerable.Repeat((byte)0x00, size / BitsPerByte).ToArray()) };
                    yield return new object[] { "byte[](alternating)", ImmutableBitArray.From(Enumerable.Repeat((byte)0xaa, size / BitsPerByte).ToArray()) };
                }
                if (size >= BitsPerInt32)
                {
                    yield return new object[] { "int[](all)", ImmutableBitArray.From(Enumerable.Repeat(unchecked((int)0xffffffff), size / BitsPerInt32).ToArray()) };
                    yield return new object[] { "int[](none)", ImmutableBitArray.From(Enumerable.Repeat(0x00000000, size / BitsPerInt32).ToArray()) };
                    yield return new object[] { "int[](alternating)", ImmutableBitArray.From(Enumerable.Repeat(unchecked((int)0xaaaaaaaa), size / BitsPerInt32).ToArray()) };
                }
            }
        }

        [Theory]
        [MemberData(nameof(Ctor_BitArraySlim_TestData))]
        public static void Ctor_BitArraySlim(string label, ImmutableBitArray bits)
        {
            _ = label;

            ImmutableBitArray bitArray = bits;
            Assert.Equal(bits.Length, bitArray.Length);
            Assert.Equal(bits, bitArray);
            for (int i = 0; i < bitArray.Length; i++)
            {
                Assert.Equal(bits[i], bitArray[i]);
                Assert.Equal(bits[i], bitArray.Get(i));
            }
        }


        public static IEnumerable<object[]> Ctor_IntArray_TestData()
        {
            yield return new object[] { new int[0], new bool[0] };
            foreach (int size in new[] { 1, 10 })
            {
                yield return new object[] { Enumerable.Repeat(unchecked((int)0xffffffff), size).ToArray(), Enumerable.Repeat(true, size * BitsPerInt32).ToArray() };
                yield return new object[] { Enumerable.Repeat(0x00000000, size).ToArray(), Enumerable.Repeat(false, size * BitsPerInt32).ToArray() };
                yield return new object[] { Enumerable.Repeat(unchecked((int)0xaaaaaaaa), size).ToArray(), Enumerable.Range(0, size * BitsPerInt32).Select(i => i % 2 == 1).ToArray() };
            }
        }

        [Theory]
        [MemberData(nameof(Ctor_IntArray_TestData))]
        public static void Ctor_IntArray(int[] array, bool[] expected)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.From(array);
            Assert.Equal(expected.Length, bitArray.Length);
            for (int i = 0; i < expected.Length; i++)
            {
                Assert.Equal(expected[i], bitArray[i]);
                Assert.Equal(expected[i], bitArray.Get(i));
            }
        }


        [Fact]
        public static void Ctor_LargeIntArrayOverflowingBitArraySlim_ThrowsArgumentException()
        {
            Assert.Throws<ArgumentException>("values", () => ImmutableBitArray.From(new int[int.MaxValue / BitsPerInt32 + 1]));
        }

        public static IEnumerable<object[]> Ctor_ByteArray_TestData()
        {
            yield return new object[] { new byte[0], new bool[0] };
            foreach (int size in new[] { 1, 2, 3, BitsPerInt32 / BitsPerByte, 2 * BitsPerInt32 / BitsPerByte })
            {
                yield return new object[] { Enumerable.Repeat((byte)0xff, size).ToArray(), Enumerable.Repeat(true, size * BitsPerByte).ToArray() };
                yield return new object[] { Enumerable.Repeat((byte)0x00, size).ToArray(), Enumerable.Repeat(false, size * BitsPerByte).ToArray() };
                yield return new object[] { Enumerable.Repeat((byte)0xaa, size).ToArray(), Enumerable.Range(0, size * BitsPerByte).Select(i => i % 2 == 1).ToArray() };
            }
        }

        [Theory]
        [MemberData(nameof(Ctor_ByteArray_TestData))]
        public static void Ctor_ByteArray(byte[] bytes, bool[] expected)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.From(bytes);
            Assert.Equal(expected.Length, bitArray.Length);
            for (int i = 0; i < bitArray.Length; i++)
            {
                Assert.Equal(expected[i], bitArray[i]);
                Assert.Equal(expected[i], bitArray.Get(i));
            }
        }


        [Fact]
        public static void Ctor_LargeByteArrayOverflowingBitArraySlim_ThrowsArgumentException()
        {
            Assert.Throws<ArgumentException>("bytes", () => ImmutableBitArray.From(new byte[int.MaxValue / BitsPerByte + 1]));
        }


        [Fact]
        public static void Clone_LongLength_Works()
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(int.MaxValue - 30);
            ImmutableBitArray clone = bitArray;

            Assert.Equal(bitArray.Length, clone.Length);
        }
    }
}
