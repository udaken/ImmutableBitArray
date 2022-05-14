// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using Xunit;

namespace Collections.Immutable.Tests
{
    public static class BitArray_GetSetTests
    {
        private const int BitsPerByte = 8;
        private const int BitsPerInt32 = 32;

        public static IEnumerable<object[]> Get_Set_Data()
        {
            foreach (int size in new[] { 0, 1, BitsPerByte, BitsPerByte * 2, BitsPerInt32, BitsPerInt32 * 2 })
            {
                foreach (bool def in new[] { true, false })
                {
                    yield return new object[] { def, Enumerable.Repeat(true, size).ToArray() };
                    yield return new object[] { def, Enumerable.Repeat(false, size).ToArray() };
                    yield return new object[] { def, Enumerable.Range(0, size).Select(i => i % 2 == 1).ToArray() };
                }
            }
        }

        [Theory]
        [MemberData(nameof(Get_Set_Data))]
        public static void Get_Set(bool defaultValue, bool[] newValues)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(newValues.Length, defaultValue);
            for (int i = 0; i < newValues.Length; i++)
            {
                bitArray = bitArray.Set(i, newValues[i]);
                Assert.Equal(newValues[i], bitArray[i]);
                Assert.Equal(newValues[i], bitArray.Get(i));
            }
        }

        [Fact]
        public static void Get_InvalidIndex_ThrowsArgumentOutOfRangeException()
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(4);
            Assert.Throws<ArgumentOutOfRangeException>("index", () => bitArray.Get(-1));
            Assert.Throws<ArgumentOutOfRangeException>("index", () => bitArray.Get(bitArray.Length));

            Assert.Throws<ArgumentOutOfRangeException>("index", () => bitArray[-1]);
            Assert.Throws<ArgumentOutOfRangeException>("index", () => bitArray[bitArray.Length]);
        }

        [Fact]
        public static void Set_InvalidIndex_ThrowsArgumentOutOfRangeException()
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(4);
            Assert.Throws<ArgumentOutOfRangeException>("index", () => bitArray.Set(-1, true));
            Assert.Throws<ArgumentOutOfRangeException>("index", () => bitArray.Set(bitArray.Length, true));

        }

        public static IEnumerable<object[]> GetEnumerator_Data()
        {
            foreach (int size in new[] { 0, 1, BitsPerByte, BitsPerByte + 1, BitsPerInt32, BitsPerInt32 + 1 })
            {
                foreach (bool lead in new[] { true, false })
                {
                    yield return new object[] { Enumerable.Range(0, size).Select(i => lead ^ (i % 2 == 0)).ToArray() };
                }
            }
        }

        [Theory]
        [MemberData(nameof(GetEnumerator_Data))]
        public static void GetEnumerator(bool[] values)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.From(values);
            Assert.NotEqual(bitArray.GetEnumerator(), bitArray.GetEnumerator());
            IEnumerator enumerator = bitArray.GetEnumerator();
            for (int i = 0; i < 2; i++)
            {
                int counter = 0;
                while (enumerator.MoveNext())
                {
                    Assert.Equal(bitArray[counter], enumerator.Current);
                    counter++;
                }
                Assert.Equal(bitArray.Length, counter);
                enumerator.Reset();
            }
        }

        [Theory]
        [InlineData(0)]
        [InlineData(1)]
        [InlineData(BitsPerByte)]
        [InlineData(BitsPerByte + 1)]
        [InlineData(BitsPerInt32)]
        [InlineData(BitsPerInt32 + 1)]
        public static void GetEnumerator_Invalid(int size)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(size, true);
            IEnumerator<bool> enumerator = bitArray.GetEnumerator();

            // Has not started enumerating
            Assert.Throws<InvalidOperationException>(() => enumerator.Current);

            // Has finished enumerating
            while (enumerator.MoveNext())
            {
            }

            Assert.Throws<InvalidOperationException>(() => enumerator.Current);

            // Has resetted enumerating
            enumerator.Reset();
            Assert.Throws<InvalidOperationException>(() => enumerator.Current);

            // Has modified underlying collection
            if (size > 0)
            {
                enumerator.MoveNext();
                bitArray = bitArray.Set(0, false);
                Assert.True(enumerator.Current);
            }
        }

        [Fact]
        public static void GetEnumerator_CloneEnumerator_ReturnsUniqueEnumerator()
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(1);
            IEnumerator<bool> enumerator = bitArray.GetEnumerator();
            ICloneable cloneableEnumerator = (ICloneable)enumerator;
            Assert.NotNull(cloneableEnumerator);

            IEnumerator clonedEnumerator = (IEnumerator)cloneableEnumerator.Clone();
            Assert.NotSame(enumerator, clonedEnumerator);

            Assert.True(clonedEnumerator.MoveNext());
            Assert.False(clonedEnumerator.MoveNext());

            Assert.True(enumerator.MoveNext());
            Assert.False(enumerator.MoveNext());
        }

        public static IEnumerable<object[]> Length_Set_Data()
        {
            int[] sizes = { 1, BitsPerByte, BitsPerByte + 1, BitsPerInt32, BitsPerInt32 + 1 };
            foreach (int original in sizes.Concat(new[] { 16384 }))
            {
                foreach (int n in sizes)
                {
                    yield return new object[] { original, n };
                }
            }
        }

        [Theory]
        [InlineData(0, 32)]
        [InlineData(0, 64)]
        [InlineData(1, 32)]
        [InlineData(1, 64)]
        [InlineData(32, 65)]
        [InlineData(64, 65)]
        [InlineData(64, 128)]
        public static void Expand(int initSize, int newSize)
        {
            Assert.All(ImmutableBitArray.Create(initSize, false).Resize(newSize), elem => Assert.False(elem));

            ImmutableBitArray bitarray = ImmutableBitArray.Create(initSize, true).Resize(newSize);
            Assert.All(bitarray.Take(initSize), elem => Assert.True(elem));
            Assert.All(bitarray.Skip(initSize), elem => Assert.False(elem));
        }
        [Theory]
        [InlineData(32, 0)]
        [InlineData(64, 0)]
        [InlineData(32, 1)]
        [InlineData(64, 1)]
        [InlineData(65, 32)]
        [InlineData(65, 64)]
        [InlineData(128, 64)]
        public static void Shrink(int initSize, int newSize)
        {
            Assert.All(ImmutableBitArray.Create(initSize, false).Resize(newSize), elem => Assert.False(elem));

            ImmutableBitArray bitarray = ImmutableBitArray.Create(initSize, true).Resize(newSize);
            Assert.All(bitarray, elem => Assert.True(elem));
        }


        [Theory]
        [MemberData(nameof(Length_Set_Data))]
        public static void Length_Set(int originalSize, int newSize)
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(originalSize, true).Resize(newSize);
            Assert.Equal(newSize, bitArray.Length);
            for (int i = 0; i < Math.Min(originalSize, bitArray.Length); i++)
            {
                Assert.True(bitArray[i]);
                Assert.True(bitArray.Get(i));
            }
            for (int i = originalSize; i < newSize; i++)
            {
                Assert.False(bitArray[i]);
                Assert.False(bitArray.Get(i));
            }
            Assert.Throws<ArgumentOutOfRangeException>("index", () => bitArray[newSize]);
            Assert.Throws<ArgumentOutOfRangeException>("index", () => bitArray.Get(newSize));

            // Decrease then increase size
            bitArray = bitArray.Resize(0);
            Assert.Equal(0, bitArray.Length);

            bitArray = bitArray.Resize(newSize);
            Assert.Equal(newSize, bitArray.Length);
            Assert.False(bitArray.Get(0));
            Assert.False(bitArray.Get(newSize - 1));
        }

        [Fact]
        public static void Length_Set_InvalidLength_ThrowsArgumentOutOfRangeException()
        {
            ImmutableBitArray bitArray = ImmutableBitArray.Create(1);
            Assert.Throws<ArgumentOutOfRangeException>(() => bitArray.Resize(-1));
        }

        public static IEnumerable<object[]> CopyTo_Array_TestData()
        {
            yield return new object[] { ImmutableBitArray.Create(0), 0, 0, new bool[0], default(bool) };
            yield return new object[] { ImmutableBitArray.Create(0), 0, 0, new byte[0], default(byte) };
            yield return new object[] { ImmutableBitArray.Create(0), 0, 0, new int[0], default(int) };

            foreach (int bitArraySize in new[] { 0, 1, BitsPerByte, BitsPerByte * 2, BitsPerInt32, BitsPerInt32 * 2, BitsPerInt32 * 4, BitsPerInt32 * 8, BitsPerInt32 * 16 })
            {
                ImmutableBitArray allTrue = ImmutableBitArray.Create(bitArraySize, true);
                ImmutableBitArray allFalse = ImmutableBitArray.Create(bitArraySize, false);
                ImmutableBitArray alternating = ImmutableBitArray.From(Enumerable.Range(0, bitArraySize).Select(i => i % 2 == 1).ToArray());

                Random rnd = new Random(0);

                foreach ((int arraySize, int startIndex) in new[] { (bitArraySize, 0),
                                                               (bitArraySize * 2 + 1, 0),
                                                               (bitArraySize * 2 + 1, bitArraySize + 1),
                                                               (bitArraySize * 2 + 1, bitArraySize / 2 + 1) })
                {
                    yield return new object[] { allTrue, arraySize, startIndex, Enumerable.Repeat(true, bitArraySize).ToArray(), default(bool) };
                    yield return new object[] { allFalse, arraySize, startIndex, Enumerable.Repeat(false, bitArraySize).ToArray(), default(bool) };
                    yield return new object[] { alternating, arraySize, startIndex, Enumerable.Range(0, bitArraySize).Select(i => i % 2 == 1).ToArray(), default(bool) };

                    bool[] randomBools = new bool[bitArraySize];
                    for (int i = 0; i < bitArraySize; i++)
                    {
                        randomBools[i] = rnd.Next(0, 2) == 0;
                    }
                    ImmutableBitArray random = ImmutableBitArray.From(randomBools);

                    yield return new object[] { random, arraySize, startIndex, randomBools, default(bool) };

                    if (bitArraySize >= BitsPerByte)
                    {
                        yield return new object[] { allTrue, arraySize / BitsPerByte, startIndex / BitsPerByte, Enumerable.Repeat((byte)0xff, bitArraySize / BitsPerByte).ToArray(), default(byte) };
                        yield return new object[] { allFalse, arraySize / BitsPerByte, startIndex / BitsPerByte, Enumerable.Repeat((byte)0x00, bitArraySize / BitsPerByte).ToArray(), default(byte) };
                        yield return new object[] { alternating, arraySize / BitsPerByte, startIndex / BitsPerByte, Enumerable.Repeat((byte)0xaa, bitArraySize / BitsPerByte).ToArray(), default(byte) };
                    }

                    if (bitArraySize >= BitsPerInt32)
                    {
                        yield return new object[] { allTrue, arraySize / BitsPerInt32, startIndex / BitsPerInt32, Enumerable.Repeat(unchecked((int)0xffffffff), bitArraySize / BitsPerInt32).ToArray(), default(int) };
                        yield return new object[] { allFalse, arraySize / BitsPerInt32, startIndex / BitsPerInt32, Enumerable.Repeat(0x00000000, bitArraySize / BitsPerInt32).ToArray(), default(int) };
                        yield return new object[] { alternating, arraySize / BitsPerInt32, startIndex / BitsPerInt32, Enumerable.Repeat(unchecked((int)0xaaaaaaaa), bitArraySize / BitsPerInt32).ToArray(), default(int) };
                    }
                }
            }

            foreach (int bitArraySize in new[] { BitsPerInt32 - 1, BitsPerInt32 * 2 - 1 })
            {
                ImmutableBitArray allTrue = ImmutableBitArray.Create(bitArraySize, true);
                ImmutableBitArray allFalse = ImmutableBitArray.Create(bitArraySize, false);
                ImmutableBitArray alternating = ImmutableBitArray.From(Enumerable.Range(0, bitArraySize).Select(i => i % 2 == 1).ToArray());
                foreach ((int arraySize, int startIndex) in new[] { (bitArraySize, 0),
                                                               (bitArraySize * 2 + 1, 0),
                                                               (bitArraySize * 2 + 1, bitArraySize + 1),
                                                               (bitArraySize * 2 + 1, bitArraySize / 2 + 1) })
                {

                    if (bitArraySize >= BitsPerInt32)
                    {
                        yield return new object[] { allTrue, (arraySize - 1) / BitsPerInt32 + 1, startIndex / BitsPerInt32, Enumerable.Repeat(unchecked((int)0xffffffff), bitArraySize / BitsPerInt32).Concat(new[] { unchecked((int)(0xffffffffu >> 1)) }).ToArray(), default(int) };
                        yield return new object[] { allFalse, (arraySize - 1) / BitsPerInt32 + 1, startIndex / BitsPerInt32, Enumerable.Repeat(0x00000000, bitArraySize / BitsPerInt32 + 1).ToArray(), default(int) };
                        yield return new object[] { alternating, (arraySize - 1) / BitsPerInt32 + 1, startIndex / BitsPerInt32, Enumerable.Repeat(unchecked((int)0xaaaaaaaa), bitArraySize / BitsPerInt32).Concat(new[] { unchecked((int)(0xaaaaaaaau >> 2)) }).ToArray(), default(int) };
                    }
                }
            }
        }


        [Theory]
        [MemberData(nameof(CopyTo_Array_TestData))]
        public static void CopyTo<T>(ImmutableBitArray bitArray, int destinationLength, int startIndex, T[] expected, T def)
            where T : notnull
        {
            T[] array = new T[destinationLength];
            if (typeof(T) == typeof(int))
            {
                bitArray.CopyTo((array as int[]).AsSpan(startIndex));
            }
            else if (typeof(T) == typeof(byte))
            {
                bitArray.CopyTo((array as byte[]).AsSpan(startIndex));
            }
            else if (typeof(T) == typeof(bool))
            {
                bitArray.CopyTo((array as bool[]).AsSpan(startIndex));
            }
            else
            {
                throw new Exception();
            }

            for (int i = 0; i < startIndex; i++)
            {
                Assert.True(def.Equals(array[i]), $"Elements before the start index have been modified. Expected {def} at index {i}, actual {array[i]}");
            }
            for (int i = 0; i < expected.Length; i++)
            {
                Assert.True(expected[i].Equals(array[i + startIndex]), $"Elements that are copied over does not match the expected value. Expected {expected[i]} at index {i + startIndex}, actual {array[i]}");
            }
            for (int i = startIndex + expected.Length; i < array.Length; i++)
            {
                Assert.True(def.Equals(array[i]), $"Elements after the copied area have been modified. Expected {def} at index {i}, actual {array[i]}");
            }
        }

        [Fact]
        public static void CopyToByteArray()
        {
            for (int size = 4; size < 100; size++)
            {
                var bitArray = ImmutableBitArray.Create(size);
                bitArray = bitArray.Set(1, true).Set(3, true);

                for (int i = 0; i < 100; i++)
                {
                    byte[] expectedOutput = new byte[100 + (size / 8 + 1)];
                    byte[] actualOutput = new byte[expectedOutput.Length];

                    expectedOutput[i] = 10;
                    bitArray.CopyTo(actualOutput.AsSpan(i));

                    Assert.Equal(expectedOutput, actualOutput);
                }
            }
        }

        [Fact]
        public static void CopyToBoolArray()
        {
            for (int size = 4; size < 100; size++)
            {
                var bitArray = ImmutableBitArray.Create(size);
                bitArray = bitArray.SetMultipleBits(true, 1, 3);

                for (int i = 0; i < 100; i++)
                {
                    bool[] expectedOutput = new bool[100 + size];
                    bool[] actualOutput = new bool[expectedOutput.Length];

                    expectedOutput[i + 1] = true;
                    expectedOutput[i + 3] = true;
                    bitArray.CopyTo(actualOutput.AsSpan(i));

                    Assert.Equal(expectedOutput, actualOutput);
                }
            }
        }

        [Fact]
        public static void CopyToIntArray()
        {
            for (int size = 10; size < 100; size++)
            {
                var bitArray = ImmutableBitArray.Create(size);
                bitArray = bitArray.SetMultipleBits(true, 1, 3, 9);

                for (int i = 0; i < 100; i++)
                {
                    int[] expectedOutput = new int[100 + (size / 32 + 1)];
                    int[] actualOutput = new int[expectedOutput.Length];

                    expectedOutput[i] = 522;
                    bitArray.CopyTo(actualOutput.AsSpan(i));

                    Assert.Equal(expectedOutput, actualOutput);
                }
            }
        }

        // https://github.com/dotnet/runtime/issues/30440
        [Fact]
        public static void CopyToByteArray_Regression39929()
        {
            bool[] directionBools = { true, true, true, true };
            bool[] levelBools = { false, false, false, true };
            byte[] byteHolder = new byte[2];
            ImmutableBitArray directionBits = ImmutableBitArray.From(directionBools);
            ImmutableBitArray levelBits = ImmutableBitArray.From(levelBools);

            directionBits.CopyTo(byteHolder.AsSpan(0));
            levelBits.CopyTo(byteHolder.AsSpan(1));

            byte[] expectedOutput = { 0x0F, 0x08 };
            Assert.Equal(expectedOutput, byteHolder);
        }

        // https://github.com/dotnet/core/issues/3194
        [Fact]
        public static void CopyToByteArray_Regression3194()
        {
            byte[] actualOutput = new byte[10];
            ImmutableBitArray bitArray = ImmutableBitArray.Create(1);
            bitArray = bitArray.Set(0, true);

            bitArray.CopyTo(actualOutput.AsSpan(5));

            byte[] expectedOutput = new byte[10];
            expectedOutput[5] = 1;
            Assert.Equal(expectedOutput, actualOutput);
        }

        [Theory]
        [InlineData(default(bool), 1, 0)]
        [InlineData(default(bool), BitsPerByte, BitsPerByte - 1)]
        [InlineData(default(bool), BitsPerInt32, BitsPerInt32 - 1)]
        [InlineData(default(byte), BitsPerByte, 0)]
        [InlineData(default(byte), BitsPerByte * 4, 4 - 1)]
        [InlineData(default(int), BitsPerInt32, 0)]
        [InlineData(default(int), BitsPerInt32 * 4, 4 - 1)]
        public static void CopyTo_Size_Invalid<T>(T def, int bits, int arraySize)
        {
            var bitArray = ImmutableBitArray.Create(bits);
            T[] array = (T[])Array.CreateInstance(typeof(T), arraySize);
            if (def is int)
            {
                Assert.Throws<ArgumentException>("destination", NewMethod(bitArray, array));
            }
            else
            {
                Assert.Throws<ArgumentException>(null, NewMethod(bitArray, array));
            }

            static Action NewMethod(ImmutableBitArray bitArray, T[] array) => () =>
            {
                if (typeof(T) == typeof(int))
                {
                    bitArray.CopyTo((array as int[]));
                }
                else if (typeof(T) == typeof(byte))
                {
                    bitArray.CopyTo((array as byte[]));
                }
                else if (typeof(T) == typeof(bool))
                {
                    bitArray.CopyTo((array as bool[]));
                }
                else
                {
                    throw new Exception();
                }
            };
        }

        public static IEnumerable<object[]> CopyTo_Hidden_Data()
        {
            yield return new object[] { "ZeroLength", ImmutableBitArray.Create(0) };
            yield return new object[] { "Constructor", ImmutableBitArray.Create(BitsPerInt32 / 2 - 3, true) };
            yield return new object[] { "Not", ImmutableBitArray.Create(BitsPerInt32 / 2 - 3, false).Not() };
            ImmutableBitArray setAll = ImmutableBitArray.Create(BitsPerInt32 / 2 - 3, true);
            yield return new object[] { "SetAll", setAll };
            ImmutableBitArray lengthShort = ImmutableBitArray.Create(BitsPerInt32, true).Resize(BitsPerInt32 / 2 - 3);
            yield return new object[] { "Length-Short", lengthShort };
            ImmutableBitArray lengthLong = ImmutableBitArray.Create(2 * BitsPerInt32, true).Resize(BitsPerInt32 - 3);
            yield return new object[] { "Length-Long < 32", lengthLong };
            ImmutableBitArray lengthLong2 = ImmutableBitArray.Create(2 * BitsPerInt32, true).Resize(BitsPerInt32 + 3);

            yield return new object[] { "Length-Long > 32", lengthLong2 };
            // alligned test cases
            yield return new object[] { "Aligned-Constructor", ImmutableBitArray.Create(BitsPerInt32, true) };
            yield return new object[] { "Aligned-Not", ImmutableBitArray.Create(BitsPerInt32, false).Not() };
            ImmutableBitArray alignedSetAll = ImmutableBitArray.Create(BitsPerInt32, true);
            yield return new object[] { "Aligned-SetAll", alignedSetAll };
            ImmutableBitArray alignedLengthLong = ImmutableBitArray.Create(2 * BitsPerInt32, true);
            yield return new object[] { "Aligned-Length-Long", alignedLengthLong };
        }

        [Theory]
        [MemberData(nameof(CopyTo_Hidden_Data))]
        public static void CopyTo_Int_Hidden(string label, ImmutableBitArray bits)
        {
            _ = label;

            int allBitsSet = unchecked((int)0xffffffff); // 32 bits set to 1 = -1
            int fullInts = bits.Length / BitsPerInt32;
            int remainder = bits.Length % BitsPerInt32;
            int arrayLength = fullInts + (remainder > 0 ? 1 : 0);

            int[] data = new int[arrayLength];
            bits.CopyTo(data);

            Assert.All(data.Take(fullInts), d => Assert.Equal(allBitsSet, d));

            if (remainder > 0)
            {
                Assert.Equal((1 << remainder) - 1, data[fullInts]);
            }
        }

        [Theory]
        [MemberData(nameof(CopyTo_Hidden_Data))]
        public static void CopyTo_Byte_Hidden(string label, ImmutableBitArray bits)
        {
            _ = label;

            byte allBitsSet = (1 << BitsPerByte) - 1; // 8 bits set to 1 = 255

            int fullBytes = bits.Length / BitsPerByte;
            int remainder = bits.Length % BitsPerByte;
            int arrayLength = fullBytes + (remainder > 0 ? 1 : 0);

            byte[] data = new byte[arrayLength];
            bits.CopyTo(data);

            Assert.All(data.Take(fullBytes), d => Assert.Equal(allBitsSet, d));

            if (remainder > 0)
            {
                Assert.Equal((byte)((1 << remainder) - 1), data[fullBytes]);
            }
        }
    }
}
