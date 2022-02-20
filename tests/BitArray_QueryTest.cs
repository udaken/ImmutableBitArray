// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Collections.Generic;
using System.Linq;
using Xunit;

namespace Collections.Immutable.Tests
{

    public static class BitArray_QueryTest
    {

        public static IEnumerable<object[]> ToBinaryLiteral_Data()
        {
            yield return new object[] { "", default(ImmutableBitArray) };
            yield return new object[] { "0b0", ImmutableBitArray.Create(1, false) };
            yield return new object[] { "0b1", ImmutableBitArray.Create(1, true) };
            yield return new object[] { "0b00000000000000000000000000000000000000000000000000000000000000000", ImmutableBitArray.Create(65, false) };
            yield return new object[] { "0b11111111111111111111111111111111111111111111111111111111111111111", ImmutableBitArray.Create(65, true) };
            const int LongBitLength = 256 * sizeof(int) * 1;
            yield return new object[] { "0b" + new string('0', LongBitLength), ImmutableBitArray.Create(LongBitLength, false) };
            yield return new object[] { "0b" + new string('1', LongBitLength), ImmutableBitArray.Create(LongBitLength, true) };
            yield return new object[] { "0b01001011", ImmutableBitArray.From(true, true, false, true, false, false, true, false) };
            yield return new object[] { "0b00000000000000000000101011110000", ImmutableBitArray.From(new int[] { 0b00000000000000000000101011110000 }) };

        }

        [Theory]
        [MemberData(nameof(ToBinaryLiteral_Data))]
        public static void ToBinaryLiteral(string expectValue, ImmutableBitArray bitArray)
        {
            Assert.Equal(expectValue, bitArray.ToBinaryLiteral());
        }

        public static IEnumerable<object[]> PopCount_Data()
        {
            yield return new object[] { 0, default(ImmutableBitArray) };
            yield return new object[] { 0, ImmutableBitArray.Create(0) };
            yield return new object[] { 0, ImmutableBitArray.Create(1, ImmutableBitArray.ValuePattern.Zero) };
            yield return new object[] { 1, ImmutableBitArray.Create(1, ImmutableBitArray.ValuePattern.FilledOne) };
            yield return new object[] { 0, ImmutableBitArray.Create(65, ImmutableBitArray.ValuePattern.Zero) };
            yield return new object[] { 65, ImmutableBitArray.Create(65, ImmutableBitArray.ValuePattern.FilledOne) };
            yield return new object[] { 1, ImmutableBitArray.Create(65, ImmutableBitArray.ValuePattern.Zero).Set(0, true) };
            yield return new object[] { 1, ImmutableBitArray.Create(65, ImmutableBitArray.ValuePattern.Zero).Set(64, true) };
            yield return new object[] { 64, ImmutableBitArray.Create(65, ImmutableBitArray.ValuePattern.FilledOne).Set(0, false) };
            yield return new object[] { 64, ImmutableBitArray.Create(65, ImmutableBitArray.ValuePattern.FilledOne).Set(64, false) };
        }
        [Theory]
        [MemberData(nameof(PopCount_Data))]
        public static void PopCount(int expect, ImmutableBitArray bitarray)
        {
            Assert.Equal(expect, bitarray.PopCount());
        }

    }
}
