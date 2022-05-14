// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Numerics;
using System.Buffers.Binary;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
#if NETCOREAPP3_0_OR_GREATER
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;
using System.Runtime.Intrinsics.Arm;
#endif

namespace Collections.Immutable
{
    // A vector of bits.  Use this to store bits efficiently, without having to do bit
    // shifting yourself.
    public readonly struct ImmutableBitArray : IEquatable<ImmutableBitArray>, IEnumerable<bool>, IReadOnlyList<bool>
    {
        private const int BitsOfBackField = sizeof(long) * BitsPerByte;
        private const int PreallocatedArrayLength = 256;

        private static readonly int[] s_AllZero = new int[PreallocatedArrayLength];
        private static readonly int[] s_AllMinusOne;

        public enum ValuePattern
        {
            Zero,
            FilledOne,
        }


        private readonly long m_backfield;
        private readonly int[]? m_array;
        private readonly int m_bitlength;

        static ImmutableBitArray()
        {
            s_AllMinusOne = new int[PreallocatedArrayLength];
            Array.Fill(s_AllMinusOne, -1);
        }

        private ReadOnlySpan<int> IntSpan
        {
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            get
            {
                return m_array is not null ? m_array.AsSpan() :
                    MemoryMarshal.Cast<long, int>(MemoryMarshal.CreateReadOnlySpan(ref Unsafe.AsRef(in m_backfield), 1));
            }
        }

        private static Span<int> GetMutableSpan(ref long backfield, int[]? array)
        {
            return array is not null ? array.AsSpan() :
                MemoryMarshal.Cast<long, int>(MemoryMarshal.CreateSpan(ref backfield, 1));
        }

        public ReadOnlySpan<int> AsInt32Span()
        {
            return IntSpan[..GetInt32ArrayLengthFromBitLength(m_bitlength)];
        }

        public ReadOnlySpan<byte> AsByteSpan()
        {
            return MemoryMarshal.AsBytes(IntSpan)[..GetByteArrayLengthFromBitLength(m_bitlength)];
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        internal void Deconstruct(out long backfield, out int[]? array, out int bitlength)
        {
            backfield = m_backfield;
            array = m_array?.Clone() as int[];
            bitlength = m_bitlength;
        }

        public static ImmutableBitArray From(BitArray other)
        {
            if (other == null) throw new ArgumentNullException(nameof(other));
            var length = GetInt32ArrayLengthFromBitLength(other.Length);
            if (length == 0)
                return default;

            var array = new int[length];
            other.CopyTo(array, 0);
            return new ImmutableBitArray(0L, array, other.Length);
        }

        /*=========================================================================
        ** Allocates space to hold length bit values. All of the values in the bit
        ** array are set to false.
        **
        ** Exceptions: ArgumentException if length < 0.
        =========================================================================*/
        public static ImmutableBitArray Create(int length) => Create(length, false);

        /*=========================================================================
        ** Allocates space to hold length bit values. All of the values in the bit
        ** array are set to defaultValue.
        **
        ** Exceptions: ArgumentOutOfRangeException if length < 0.
        =========================================================================*/
        public static ImmutableBitArray Create(int length, bool defaultValue)
        {
            return Create(length, defaultValue ? ValuePattern.FilledOne : ValuePattern.Zero);
        }
        public static ImmutableBitArray Create(int length, ValuePattern defaultValue)
        {
            if (length < 0)
            {
                throw new ArgumentOutOfRangeException(nameof(length), length, SR.ArgumentOutOfRange_NeedNonNegNum);
            }

            Debug.Assert(Array.TrueForAll(s_AllMinusOne, i => i == -1));
            Debug.Assert(Array.TrueForAll(s_AllZero, i => i == 0));

            if (length <= BitsOfBackField)
            {
                // clear high bit values in the last int
                int extraBits = length % BitsOfBackField;
                long val = defaultValue == ValuePattern.FilledOne ? -1 : 0;
                if (defaultValue == ValuePattern.FilledOne && extraBits > 0)
                {
                    val = (1L << extraBits) - 1;
                }

                return new ImmutableBitArray(val, null, length);
            }

            if (length <= PreallocatedArrayLength * BitsPerInt32)
            {
                return new ImmutableBitArray(0, defaultValue == ValuePattern.FilledOne ? s_AllMinusOne : s_AllZero, length);
            }

            var array = new int[GetInt32ArrayLengthFromBitLength(length)];
            var backfield = 0L;

            if (defaultValue == ValuePattern.FilledOne)
            {
                var span = array.AsSpan();
                span.Fill(-1);

                // clear high bit values in the last int
                Div32Rem(length, out int extraBits);
                if (extraBits > 0)
                {
                    span[^1] = (1 << extraBits) - 1;
                }
            }
            return new ImmutableBitArray(backfield, array, length);
        }

        /*=========================================================================
        ** Allocates space to hold the bit values in bytes. bytes[0] represents
        ** bits 0 - 7, bytes[1] represents bits 8 - 15, etc. The LSB of each byte
        ** represents the lowest index value; bytes[0] & 1 represents bit 0,
        ** bytes[0] & 2 represents bit 1, bytes[0] & 4 represents bit 2, etc.
        =========================================================================*/
        public static ImmutableBitArray From(ReadOnlySpan<byte> bytes)
        {
            // this value is chosen to prevent overflow when computing m_length.
            // m_length is of type int32 and is exposed as a property, so
            // type of m_length can't be changed to accommodate.
            if (bytes.Length > int.MaxValue / BitsPerByte)
            {
                throw new ArgumentException(SR.Format(SR.Argument_ArrayTooLarge, BitsPerByte), nameof(bytes));
            }

            var array = new int[GetInt32ArrayLengthFromByteLength(bytes.Length)];
            var bitlength = bytes.Length * BitsPerByte;
            var backfield = 0L;
            var span = GetMutableSpan(ref backfield, array);

            uint totalCount = (uint)bytes.Length / 4;

            ReadOnlySpan<byte> byteSpan = bytes;
            for (int i = 0; i < totalCount; i++)
            {
                span[i] = BinaryPrimitives.ReadInt32LittleEndian(byteSpan);
                byteSpan = byteSpan[4..];
            }

            Debug.Assert(byteSpan.Length >= 0 && byteSpan.Length < 4);

            int last = 0;
            switch (byteSpan.Length)
            {
                case 3:
                    last = byteSpan[2] << 16;
                    goto case 2;
                // fall through
                case 2:
                    last |= byteSpan[1] << 8;
                    goto case 1;
                // fall through
                case 1:
                    span[(int)totalCount] = last | byteSpan[0];
                    break;
            }
            return new ImmutableBitArray(backfield, array, bitlength);
        }

        private const uint Vector128ByteCount = 16;
        private const uint Vector128IntCount = 4;
        private const uint Vector256ByteCount = 32;
        private const uint Vector256IntCount = 8;

        public static ImmutableBitArray From(params bool[] values)
            => From((values ?? throw new ArgumentNullException(nameof(values))).AsSpan());

        public static unsafe ImmutableBitArray From(ReadOnlySpan<bool> values)
        {
            var array = values.Length > BitsOfBackField ? new int[GetInt32ArrayLengthFromBitLength(values.Length)] : null;
            var bitlength = values.Length;
            var backfield = 0L;

            var span = GetMutableSpan(ref backfield, array);

            uint i = 0;

#if NETCOREAPP3_0_OR_GREATER
            if (values.Length < Vector256<byte>.Count)
            {
                goto LessThan32;
            }

            // Comparing with 1s would get rid of the final negation, however this would not work for some CLR bools
            // (true for any non-zero values, false for 0) - any values between 2-255 will be interpreted as false.
            // Instead, We compare with zeroes (== false) then negate the result to ensure compatibility.

            if (Avx2.IsSupported)
            {
                // JIT does not support code hoisting for SIMD yet
                Vector256<byte> zero = Vector256<byte>.Zero;
                fixed (bool* ptr = values)
                {
                    for (; (i + Vector256ByteCount) <= (uint)values.Length; i += Vector256ByteCount)
                    {
                        Vector256<byte> vector = Avx.LoadVector256((byte*)ptr + i);
                        Vector256<byte> isFalse = Avx2.CompareEqual(vector, zero);
                        int result = Avx2.MoveMask(isFalse);
                        span[(int)(i / 32u)] = ~result;
                    }
                }
            }
            else if (Sse2.IsSupported)
            {
                // JIT does not support code hoisting for SIMD yet
                Vector128<byte> zero = Vector128<byte>.Zero;
                fixed (bool* ptr = values)
                {
                    for (; (i + Vector128ByteCount * 2u) <= (uint)values.Length; i += Vector128ByteCount * 2u)
                    {
                        Vector128<byte> lowerVector = Sse2.LoadVector128((byte*)ptr + i);
                        Vector128<byte> lowerIsFalse = Sse2.CompareEqual(lowerVector, zero);
                        int lowerPackedIsFalse = Sse2.MoveMask(lowerIsFalse);

                        Vector128<byte> upperVector = Sse2.LoadVector128((byte*)ptr + i + Vector128<byte>.Count);
                        Vector128<byte> upperIsFalse = Sse2.CompareEqual(upperVector, zero);
                        int upperPackedIsFalse = Sse2.MoveMask(upperIsFalse);

                        span[(int)(i / 32u)] = ~((upperPackedIsFalse << 16) | lowerPackedIsFalse);
                    }
                }
            }
            else if (AdvSimd.Arm64.IsSupported)
            {
                // JIT does not support code hoisting for SIMD yet
                // However comparison against zero can be replaced to cmeq against zero (vceqzq_s8)
                // See dotnet/runtime#33972 for details
                Vector128<byte> zero = Vector128<byte>.Zero;
                Vector128<byte> bitMask128 = BitConverter.IsLittleEndian ?
                                             Vector128.Create(0x80402010_08040201).AsByte() :
                                             Vector128.Create(0x01020408_10204080).AsByte();

                fixed (bool* ptr = values)
                {
                    for (; (i + Vector128ByteCount * 2u) <= (uint)values.Length; i += Vector128ByteCount * 2u)
                    {
                        // Same logic as SSE2 path, however we lack MoveMask (equivalent) instruction
                        // As a workaround, mask out the relevant bit after comparison
                        // and combine by ORing all of them together (In this case, adding all of them does the same thing)
                        Vector128<byte> lowerVector = AdvSimd.LoadVector128((byte*)ptr + i);
                        Vector128<byte> lowerIsFalse = AdvSimd.CompareEqual(lowerVector, zero);
                        Vector128<byte> bitsExtracted1 = AdvSimd.And(lowerIsFalse, bitMask128);
                        bitsExtracted1 = AdvSimd.Arm64.AddPairwise(bitsExtracted1, bitsExtracted1);
                        bitsExtracted1 = AdvSimd.Arm64.AddPairwise(bitsExtracted1, bitsExtracted1);
                        bitsExtracted1 = AdvSimd.Arm64.AddPairwise(bitsExtracted1, bitsExtracted1);
                        Vector128<short> lowerPackedIsFalse = bitsExtracted1.AsInt16();

                        Vector128<byte> upperVector = AdvSimd.LoadVector128((byte*)ptr + i + Vector128<byte>.Count);
                        Vector128<byte> upperIsFalse = AdvSimd.CompareEqual(upperVector, zero);
                        Vector128<byte> bitsExtracted2 = AdvSimd.And(upperIsFalse, bitMask128);
                        bitsExtracted2 = AdvSimd.Arm64.AddPairwise(bitsExtracted2, bitsExtracted2);
                        bitsExtracted2 = AdvSimd.Arm64.AddPairwise(bitsExtracted2, bitsExtracted2);
                        bitsExtracted2 = AdvSimd.Arm64.AddPairwise(bitsExtracted2, bitsExtracted2);
                        Vector128<short> upperPackedIsFalse = bitsExtracted2.AsInt16();

                        int result = AdvSimd.Arm64.ZipLow(lowerPackedIsFalse, upperPackedIsFalse).AsInt32().ToScalar();
                        if (!BitConverter.IsLittleEndian)
                        {
                            result = BinaryPrimitives.ReverseEndianness(result);
                        }
                        span[(int)(i / 32u)] = ~result;
                    }
                }
            }

        LessThan32:
#endif
            for (; i < (uint)values.Length; i++)
            {
                if (values[(int)i])
                {
                    int elementIndex = Div32Rem((int)i, out int extraBits);
                    span[elementIndex] |= 1 << extraBits;
                }
            }

            return new ImmutableBitArray(backfield, array, bitlength);
        }

        /*=========================================================================
        ** Allocates space to hold the bit values in values. values[0] represents
        ** bits 0 - 31, values[1] represents bits 32 - 63, etc. The LSB of each
        ** integer represents the lowest index value; values[0] & 1 represents bit
        ** 0, values[0] & 2 represents bit 1, values[0] & 4 represents bit 2, etc.
        =========================================================================*/
        public static unsafe ImmutableBitArray From(ReadOnlySpan<int> values)
        {
            // this value is chosen to prevent overflow when computing m_length
            if (values.Length > int.MaxValue / BitsPerInt32)
            {
                throw new ArgumentException(SR.Format(SR.Argument_ArrayTooLarge, BitsPerInt32), nameof(values));
            }

            var array = (values.Length * BitsPerInt32) > BitsOfBackField ? (new int[values.Length]) : null;
            var bitlength = values.Length * BitsPerInt32;
            var backfield = 0L;
            var span = GetMutableSpan(ref backfield, array);

            values.CopyTo(span);

            return new ImmutableBitArray(backfield, array, bitlength);
        }

        public static unsafe ImmutableBitArray From(ReadOnlySpan<ulong> values)
        {
            return From(MemoryMarshal.Cast<ulong, int>(values));
        }

        private ImmutableBitArray(long backfield, int[]? array, int length)
        {
            m_backfield = backfield;
            m_array = array;
            m_bitlength = length;


            if (m_array == null)
                Debug.Assert(m_bitlength <= BitsOfBackField);
            else
                Debug.Assert(m_bitlength <= m_array.Length * (long)BitsPerInt32);
        }

        public bool this[int index]
        {
            get => Get(index);
        }

        /*=========================================================================
        ** Returns the bit value at position index.
        **
        ** Exceptions: ArgumentOutOfRangeException if index < 0 or
        **             index >= GetLength().
        =========================================================================*/
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public bool Get(int index)
        {
            if ((uint)index >= (uint)m_bitlength)
                ThrowArgumentOutOfRangeException(index);

            int bitMask = 1 << index;
            return (IntSpan[index >> 5] & bitMask) != 0;
        }

        /*=========================================================================
        ** Sets the bit value at position index to value.
        **
        ** Exceptions: ArgumentOutOfRangeException if index < 0 or
        **             index >= GetLength().
        =========================================================================*/
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public ImmutableBitArray Set(int index, bool value)
        {
            if ((uint)index >= (uint)m_bitlength)
                ThrowArgumentOutOfRangeException(index);

            if (m_array == s_AllMinusOne && value) return this;
            if (m_array == s_AllZero && !value) return this;

            (var backfield, var array, var length) = this;
            var span = GetMutableSpan(ref backfield, array);

            int bitMask = 1 << index;
            ref int segment = ref span[index >> 5];

            if (value)
            {
                segment |= bitMask;
            }
            else
            {
                segment &= ~bitMask;
            }
            return new ImmutableBitArray(backfield, array, length);
        }

        public ImmutableBitArray SetMultipleBits(bool value, params int[] indics) => SetMultipleBits(value, indics.AsSpan());

        public ImmutableBitArray SetMultipleBits(bool value, ReadOnlySpan<int> indics)
        {
            if (m_array == s_AllMinusOne && value) return this;
            if (m_array == s_AllZero && !value) return this;

            (var backfield, var array, var length) = this;
            var span = GetMutableSpan(ref backfield, array);

            foreach (var index in indics)
            {
                if ((uint)index >= (uint)m_bitlength)
                    ThrowArgumentOutOfRangeException(index);

                int bitMask = 1 << index;
                ref int segment = ref span[index >> 5];

                if (value)
                {
                    segment |= bitMask;
                }
                else
                {
                    segment &= ~bitMask;
                }
            }
            return new ImmutableBitArray(backfield, array, length);

        }

        /*=========================================================================
        ** Returns a reference to the current instance ANDed with value.
        **
        ** Exceptions: ArgumentException if value.Length != this.Length.
        =========================================================================*/
        public unsafe ImmutableBitArray And(ImmutableBitArray value)
        {
            (var backfield, var array, var length) = this;
            var thisArray = GetMutableSpan(ref backfield, array);
            var valueArray = value.IntSpan;

            int count = GetInt32ArrayLengthFromBitLength(Length);
            if (Length != value.Length || (uint)count > (uint)thisArray.Length || (uint)count > (uint)valueArray.Length)
                throw new ArgumentException(SR.Arg_ArrayLengthsDiffer);

            // Unroll loop for count less than Vector256 size.
            switch (count)
            {
                case 7: thisArray[6] &= valueArray[6]; goto case 6;
                case 6: thisArray[5] &= valueArray[5]; goto case 5;
                case 5: thisArray[4] &= valueArray[4]; goto case 4;
                case 4: thisArray[3] &= valueArray[3]; goto case 3;
                case 3: thisArray[2] &= valueArray[2]; goto case 2;
                case 2: thisArray[1] &= valueArray[1]; goto case 1;
                case 1: thisArray[0] &= valueArray[0]; goto Done;
                case 0: goto Done;
            }

            uint i = 0;
#if NETCOREAPP3_0_OR_GREATER
            if (Avx2.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                fixed (int* rightPtr = valueArray)
                {
                    for (; i < (uint)count - (Vector256IntCount - 1u); i += Vector256IntCount)
                    {
                        Vector256<int> leftVec = Avx.LoadVector256(leftPtr + i);
                        Vector256<int> rightVec = Avx.LoadVector256(rightPtr + i);
                        Avx.Store(leftPtr + i, Avx2.And(leftVec, rightVec));
                    }
                }
            }
            else if (Sse2.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                fixed (int* rightPtr = valueArray)
                {
                    for (; i < (uint)count - (Vector128IntCount - 1u); i += Vector128IntCount)
                    {
                        Vector128<int> leftVec = Sse2.LoadVector128(leftPtr + i);
                        Vector128<int> rightVec = Sse2.LoadVector128(rightPtr + i);
                        Sse2.Store(leftPtr + i, Sse2.And(leftVec, rightVec));
                    }
                }
            }
            else if (AdvSimd.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                fixed (int* rightPtr = valueArray)
                {
                    for (; i < (uint)count - (Vector128IntCount - 1u); i += Vector128IntCount)
                    {
                        Vector128<int> leftVec = AdvSimd.LoadVector128(leftPtr + i);
                        Vector128<int> rightVec = AdvSimd.LoadVector128(rightPtr + i);
                        AdvSimd.Store(leftPtr + i, AdvSimd.And(leftVec, rightVec));
                    }
                }
            }
#endif

            for (; i < (uint)count; i++)
                thisArray[(int)i] &= valueArray[(int)i];

            Done:
            return new ImmutableBitArray(backfield, array, length);
        }

        /*=========================================================================
        ** Returns a reference to the current instance ORed with value.
        **
        ** Exceptions: ArgumentException if value == null or
        **             value.Length != this.Length.
        =========================================================================*/
        public unsafe ImmutableBitArray Or(ImmutableBitArray value)
        {
            (var backfield, var array, var length) = this;
            var thisArray = GetMutableSpan(ref backfield, array);
            var valueArray = value.IntSpan;

            int count = GetInt32ArrayLengthFromBitLength(Length);
            if (Length != value.Length || (uint)count > (uint)thisArray.Length || (uint)count > (uint)valueArray.Length)
                throw new ArgumentException(SR.Arg_ArrayLengthsDiffer);

            // Unroll loop for count less than Vector256 size.
            switch (count)
            {
                case 7: thisArray[6] |= valueArray[6]; goto case 6;
                case 6: thisArray[5] |= valueArray[5]; goto case 5;
                case 5: thisArray[4] |= valueArray[4]; goto case 4;
                case 4: thisArray[3] |= valueArray[3]; goto case 3;
                case 3: thisArray[2] |= valueArray[2]; goto case 2;
                case 2: thisArray[1] |= valueArray[1]; goto case 1;
                case 1: thisArray[0] |= valueArray[0]; goto Done;
                case 0: goto Done;
            }

            uint i = 0;
#if NETCOREAPP3_0_OR_GREATER
            if (Avx2.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                fixed (int* rightPtr = valueArray)
                {
                    for (; i < (uint)count - (Vector256IntCount - 1u); i += Vector256IntCount)
                    {
                        Vector256<int> leftVec = Avx.LoadVector256(leftPtr + i);
                        Vector256<int> rightVec = Avx.LoadVector256(rightPtr + i);
                        Avx.Store(leftPtr + i, Avx2.Or(leftVec, rightVec));
                    }
                }
            }
            else if (Sse2.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                fixed (int* rightPtr = valueArray)
                {
                    for (; i < (uint)count - (Vector128IntCount - 1u); i += Vector128IntCount)
                    {
                        Vector128<int> leftVec = Sse2.LoadVector128(leftPtr + i);
                        Vector128<int> rightVec = Sse2.LoadVector128(rightPtr + i);
                        Sse2.Store(leftPtr + i, Sse2.Or(leftVec, rightVec));
                    }
                }
            }
            else if (AdvSimd.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                fixed (int* rightPtr = valueArray)
                {
                    for (; i < (uint)count - (Vector128IntCount - 1u); i += Vector128IntCount)
                    {
                        Vector128<int> leftVec = AdvSimd.LoadVector128(leftPtr + i);
                        Vector128<int> rightVec = AdvSimd.LoadVector128(rightPtr + i);
                        AdvSimd.Store(leftPtr + i, AdvSimd.Or(leftVec, rightVec));
                    }
                }
            }
#endif

            for (; i < (uint)count; i++)
                thisArray[(int)i] |= valueArray[(int)i];

            Done:
            return new ImmutableBitArray(backfield, array, length);
        }

        /*=========================================================================
        ** Returns a reference to the current instance XORed with value.
        **
        ** Exceptions: ArgumentException if value == null or
        **             value.Length != this.Length.
        =========================================================================*/
        public unsafe ImmutableBitArray Xor(ImmutableBitArray value)
        {
            (var backfield, var array, var length) = this;
            var thisArray = GetMutableSpan(ref backfield, array);
            var valueArray = value.IntSpan;

            int count = GetInt32ArrayLengthFromBitLength(Length);
            if (Length != value.Length || (uint)count > (uint)thisArray.Length || (uint)count > (uint)valueArray.Length)
                throw new ArgumentException(SR.Arg_ArrayLengthsDiffer);

            // Unroll loop for count less than Vector256 size.
            switch (count)
            {
                case 7: thisArray[6] ^= valueArray[6]; goto case 6;
                case 6: thisArray[5] ^= valueArray[5]; goto case 5;
                case 5: thisArray[4] ^= valueArray[4]; goto case 4;
                case 4: thisArray[3] ^= valueArray[3]; goto case 3;
                case 3: thisArray[2] ^= valueArray[2]; goto case 2;
                case 2: thisArray[1] ^= valueArray[1]; goto case 1;
                case 1: thisArray[0] ^= valueArray[0]; goto Done;
                case 0: goto Done;
            }

            uint i = 0;
#if NETCOREAPP3_0_OR_GREATER
            if (Avx2.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                fixed (int* rightPtr = value.IntSpan)
                {
                    for (; i < (uint)count - (Vector256IntCount - 1u); i += Vector256IntCount)
                    {
                        Vector256<int> leftVec = Avx.LoadVector256(leftPtr + i);
                        Vector256<int> rightVec = Avx.LoadVector256(rightPtr + i);
                        Avx.Store(leftPtr + i, Avx2.Xor(leftVec, rightVec));
                    }
                }
            }
            else if (Sse2.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                fixed (int* rightPtr = valueArray)
                {
                    for (; i < (uint)count - (Vector128IntCount - 1u); i += Vector128IntCount)
                    {
                        Vector128<int> leftVec = Sse2.LoadVector128(leftPtr + i);
                        Vector128<int> rightVec = Sse2.LoadVector128(rightPtr + i);
                        Sse2.Store(leftPtr + i, Sse2.Xor(leftVec, rightVec));
                    }
                }
            }
            else if (AdvSimd.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                fixed (int* rightPtr = valueArray)
                {
                    for (; i < (uint)count - (Vector128IntCount - 1u); i += Vector128IntCount)
                    {
                        Vector128<int> leftVec = AdvSimd.LoadVector128(leftPtr + i);
                        Vector128<int> rightVec = AdvSimd.LoadVector128(rightPtr + i);
                        AdvSimd.Store(leftPtr + i, AdvSimd.Xor(leftVec, rightVec));
                    }
                }
            }
#endif

            for (; i < (uint)count; i++)
                thisArray[(int)i] ^= valueArray[(int)i];

            Done:
            return new ImmutableBitArray(backfield, array, length);
        }

        /*=========================================================================
        ** Inverts all the bit values. On/true bit values are converted to
        ** off/false. Off/false bit values are turned on/true. The current instance
        ** is updated and returned.
        =========================================================================*/
        public unsafe ImmutableBitArray Not()
        {
            if (m_array == s_AllMinusOne)
                return new ImmutableBitArray(m_backfield, s_AllZero, m_bitlength);
            else if (m_array == s_AllZero)
                return new ImmutableBitArray(m_backfield, s_AllMinusOne, m_bitlength);

            (var backfield, var array, var length) = this;
            var thisArray = GetMutableSpan(ref backfield, array);
            int count = GetInt32ArrayLengthFromBitLength(Length);

            // Unroll loop for count less than Vector256 size.
            switch (count)
            {
                case 7: thisArray[6] = ~thisArray[6]; goto case 6;
                case 6: thisArray[5] = ~thisArray[5]; goto case 5;
                case 5: thisArray[4] = ~thisArray[4]; goto case 4;
                case 4: thisArray[3] = ~thisArray[3]; goto case 3;
                case 3: thisArray[2] = ~thisArray[2]; goto case 2;
                case 2: thisArray[1] = ~thisArray[1]; goto case 1;
                case 1: thisArray[0] = ~thisArray[0]; goto Done;
                case 0: goto Done;
            }

            uint i = 0;

#if NETCOREAPP3_0_OR_GREATER
            if (Avx2.IsSupported)
            {
                Vector256<int> ones = Vector256.Create(-1);
                fixed (int* ptr = thisArray)
                {
                    for (; i < (uint)count - (Vector256IntCount - 1u); i += Vector256IntCount)
                    {
                        Vector256<int> vec = Avx.LoadVector256(ptr + i);
                        Avx.Store(ptr + i, Avx2.Xor(vec, ones));
                    }
                }
            }
            else if (Sse2.IsSupported)
            {
                Vector128<int> ones = Vector128.Create(-1);
                fixed (int* ptr = thisArray)
                {
                    for (; i < (uint)count - (Vector128IntCount - 1u); i += Vector128IntCount)
                    {
                        Vector128<int> vec = Sse2.LoadVector128(ptr + i);
                        Sse2.Store(ptr + i, Sse2.Xor(vec, ones));
                    }
                }
            }
            else if (AdvSimd.IsSupported)
            {
                fixed (int* leftPtr = thisArray)
                {
                    for (; i < (uint)count - (Vector128IntCount - 1u); i += Vector128IntCount)
                    {
                        Vector128<int> leftVec = AdvSimd.LoadVector128(leftPtr + i);
                        AdvSimd.Store(leftPtr + i, AdvSimd.Not(leftVec));
                    }
                }
            }
#endif

            for (; i < (uint)count; i++)
                thisArray[(int)i] = ~thisArray[(int)i];

            Done:
            return new ImmutableBitArray(backfield, array, length);
        }

        [EditorBrowsable(EditorBrowsableState.Never)]
        public ImmutableBitArray RightShift(int count) => LogicalRight(count);

        /*=========================================================================
        ** Shift all the bit values to right on count bits. The current instance is
        ** updated and returned.
        *
        ** Exceptions: ArgumentOutOfRangeException if count < 0
        =========================================================================*/
        public ImmutableBitArray LogicalRight(int count)
        {
            if (count <= 0)
            {
                if (count < 0)
                {
                    throw new ArgumentOutOfRangeException(nameof(count), count, SR.ArgumentOutOfRange_NeedNonNegNum);
                }

                return this;
            }

            (var backfield, var array, var length) = this;
            var span = GetMutableSpan(ref backfield, array);

            int toIndex = 0;
            int ints = GetInt32ArrayLengthFromBitLength(m_bitlength);
            if (count < m_bitlength)
            {
                // We can not use Math.DivRem without taking a dependency on System.Runtime.Extensions
                int fromIndex = Div32Rem(count, out int shiftCount);
                Div32Rem(m_bitlength, out int extraBits);
                if (shiftCount == 0)
                {
                    unchecked
                    {
                        // Cannot use `(1u << extraBits) - 1u` as the mask
                        // because for extraBits == 0, we need the mask to be 111...111, not 0.
                        // In that case, we are shifting a uint by 32, which could be considered undefined.
                        // The result of a shift operation is undefined ... if the right operand
                        // is greater than or equal to the width in bits of the promoted left operand,
                        // https://docs.microsoft.com/en-us/cpp/c-language/bitwise-shift-operators?view=vs-2017
                        // However, the compiler protects us from undefined behaviour by constraining the
                        // right operand to between 0 and width - 1 (inclusive), i.e. right_operand = (right_operand % width).
                        uint mask = uint.MaxValue >> (BitsPerInt32 - extraBits);
                        span[ints - 1] &= (int)mask;
                    }

                    IntSpan[fromIndex..ints].CopyTo(span);
                    toIndex = ints - fromIndex;
                }
                else
                {
                    int lastIndex = ints - 1;
                    unchecked
                    {
                        while (fromIndex < lastIndex)
                        {
                            uint right = (uint)IntSpan[fromIndex] >> shiftCount;
                            int left = IntSpan[++fromIndex] << (BitsPerInt32 - shiftCount);
                            span[toIndex++] = left | (int)right;
                        }
                        uint mask = uint.MaxValue >> (BitsPerInt32 - extraBits);
                        mask &= (uint)IntSpan[fromIndex];
                        span[toIndex++] = (int)(mask >> shiftCount);
                    }
                }
            }

            span[toIndex..ints].Clear();
            return new ImmutableBitArray(backfield, array, length);
        }

        [EditorBrowsable(EditorBrowsableState.Never)]
        public ImmutableBitArray LeftShift(int count) => LogicalLeft(count);

        /*=========================================================================
        ** Shift all the bit values to left on count bits. The current instance is
        ** updated and returned.
        *
        ** Exceptions: ArgumentOutOfRangeException if count < 0
        =========================================================================*/
        public ImmutableBitArray LogicalLeft(int count)
        {
            if (count <= 0)
            {
                if (count < 0)
                {
                    throw new ArgumentOutOfRangeException(nameof(count), count, SR.ArgumentOutOfRange_NeedNonNegNum);
                }

                return this;
            }

            (var backfield, var array, var length) = this;
            var span = GetMutableSpan(ref backfield, array);

            int lengthToClear;
            if (count < m_bitlength)
            {
                int lastIndex = (m_bitlength - 1) >> BitShiftPerInt32;  // Divide by 32.

                // We can not use Math.DivRem without taking a dependency on System.Runtime.Extensions
                lengthToClear = Div32Rem(count, out int shiftCount);

                if (shiftCount == 0)
                {
                    IntSpan[..(lastIndex + 1 - lengthToClear)].CopyTo(span[lengthToClear..]);
                }
                else
                {
                    int fromindex = lastIndex - lengthToClear;
                    unchecked
                    {
                        while (fromindex > 0)
                        {
                            int left = IntSpan[fromindex] << shiftCount;
                            uint right = (uint)IntSpan[--fromindex] >> (BitsPerInt32 - shiftCount);
                            span[lastIndex] = left | (int)right;
                            lastIndex--;
                        }
                        span[lastIndex] = IntSpan[fromindex] << shiftCount;
                    }
                }
            }
            else
            {
                lengthToClear = GetInt32ArrayLengthFromBitLength(m_bitlength); // Clear all
            }

            span[..lengthToClear].Clear();
            return new ImmutableBitArray(backfield, array, length);
        }
        private bool CompareToSequence(int[] array)
        {
            var intlength = GetInt32ArrayLengthFromBitLength(m_bitlength);
            var remain = intlength;
            var intSpan = AsInt32Span();
            for (int offset = 0; offset < intlength; offset += array.Length)
            {
                int length = Math.Min(array.Length, remain);
                if (!array.AsSpan(0, length).SequenceEqual(intSpan[offset..length]))
                {
                    return false;
                }
            }

            return true;
        }


        public int Length => m_bitlength;

        int IReadOnlyCollection<bool>.Count => Length;

        public ImmutableBitArray Resize(int length)
        {
            if (length < 0)
            {
                throw new ArgumentOutOfRangeException(nameof(length), length, SR.ArgumentOutOfRange_NeedNonNegNum);
            }
            else if (length == 0)
            {
                return default;
            }
            else if (length <= m_bitlength) // shrink
            {
                return new ImmutableBitArray(m_backfield, m_array, length);
            }
            else
            {
                int newints = GetInt32ArrayLengthFromBitLength(length);
                int[]? newArray = (newints * BitsPerInt32 > BitsOfBackField) ? new int[newints] : null;
                long newBackfield = m_backfield;

                var array = GetMutableSpan(ref newBackfield, newArray);
                IntSpan.CopyTo(array);


                // clear high bit values in the last int
                int last = (m_bitlength - 1) >> BitShiftPerInt32;
                Div32Rem(m_bitlength, out int bits);
                if (bits > 0)
                {
                    array[last] &= (1 << bits) - 1;
                }

                // clear remaining int values
                array.Slice(last + 1, newints - last - 1).Clear();

                return new ImmutableBitArray(newBackfield, newArray, length);
            }
        }

        public int CopyTo(Span<int> intArray)
        {
            if (m_bitlength == 0)
                return 0;

            int len = Div32Rem(m_bitlength, out int extraBits);

            if (extraBits == 0)
            {
                // we have perfect bit alignment, no need to sanitize, just copy
                AsInt32Span().CopyTo(intArray);
                return len;
            }
            else
            {
                int last = (m_bitlength - 1) >> BitShiftPerInt32;
                // do not copy the last int, as it is not completely used
                IntSpan[..last].CopyTo(intArray);

                // the last int needs to be masked
                intArray[last] = IntSpan[last] & unchecked((1 << extraBits) - 1);
                return len + 1;
            }
        }

        public int CopyTo(Span<byte> byteArray)
        {
            if (m_bitlength == 0)
                return 0;

            int arrayLength = GetByteArrayLengthFromBitLength(m_bitlength);
            if (byteArray.Length < arrayLength)
            {
                throw new ArgumentException(SR.Argument_InvalidOffLen);
            }

            // equivalent to m_length % BitsPerByte, since BitsPerByte is a power of 2
            uint extraBits = (uint)m_bitlength & (BitsPerByte - 1);
            if (extraBits > 0)
            {
                // last byte is not aligned, we will directly copy one less byte
                arrayLength -= 1;
            }

            Span<byte> span = byteArray;

            int quotient = Div4Rem(arrayLength, out int remainder);
            for (int i = 0; i < quotient; i++)
            {
                BinaryPrimitives.WriteInt32LittleEndian(span, IntSpan[i]);
                span = span[4..];
            }

            if (extraBits > 0)
            {
                Debug.Assert(span.Length > 0);
                Debug.Assert(IntSpan.Length > quotient);
                // mask the final byte
                span[remainder] = (byte)((IntSpan[quotient] >> (remainder * 8)) & ((1 << (int)extraBits) - 1));
            }

            switch (remainder)
            {
                case 3:
                    span[2] = (byte)(IntSpan[quotient] >> 16);
                    goto case 2;
                // fall through
                case 2:
                    span[1] = (byte)(IntSpan[quotient] >> 8);
                    goto case 1;
                // fall through
                case 1:
                    span[0] = (byte)IntSpan[quotient];
                    break;
            }
            return arrayLength;
        }
        public unsafe void CopyTo(Span<bool> boolArray)
        {
            if (m_bitlength == 0)
                return;

            if (boolArray.Length < m_bitlength)
            {
                throw new ArgumentException(SR.Argument_InvalidOffLen);
            }

            uint i = 0;

            if (m_bitlength < BitsPerInt32)
                goto LessThan32;
#if NETCOREAPP3_0_OR_GREATER

            // The mask used when shuffling a single int into Vector128/256.
            // On little endian machines, the lower 8 bits of int belong in the first byte, next lower 8 in the second and so on.
            // We place the bytes that contain the bits to its respective byte so that we can mask out only the relevant bits later.
            Vector128<byte> lowerShuffleMask_CopyToBoolArray = Vector128.Create(0, 0x01010101_01010101).AsByte();
            Vector128<byte> upperShuffleMask_CopyToBoolArray = Vector128.Create(0x02020202_02020202, 0x03030303_03030303).AsByte();

            if (Avx2.IsSupported)
            {
                Vector256<byte> shuffleMask = Vector256.Create(lowerShuffleMask_CopyToBoolArray, upperShuffleMask_CopyToBoolArray);
                Vector256<byte> bitMask = Vector256.Create(0x80402010_08040201).AsByte();
                Vector256<byte> ones = Vector256.Create((byte)1);

                fixed (bool* destination = &boolArray[0])
                {
                    for (; (i + Vector256ByteCount) <= (uint)m_bitlength; i += Vector256ByteCount)
                    {
                        int bits = IntSpan[(int)(i / BitsPerInt32)];
                        Vector256<int> scalar = Vector256.Create(bits);
                        Vector256<byte> shuffled = Avx2.Shuffle(scalar.AsByte(), shuffleMask);
                        Vector256<byte> extracted = Avx2.And(shuffled, bitMask);

                        // The extracted bits can be anywhere between 0 and 255, so we normalise the value to either 0 or 1
                        // to ensure compatibility with "C# bool" (0 for false, 1 for true, rest undefined)
                        Vector256<byte> normalized = Avx2.Min(extracted, ones);
                        Avx.Store((byte*)destination + i, normalized);
                    }
                }
            }
            else if (Ssse3.IsSupported)
            {
                Vector128<byte> lowerShuffleMask = lowerShuffleMask_CopyToBoolArray;
                Vector128<byte> upperShuffleMask = upperShuffleMask_CopyToBoolArray;
                Vector128<byte> ones = Vector128.Create((byte)1);
                Vector128<byte> bitMask128 = BitConverter.IsLittleEndian ?
                                             Vector128.Create(0x80402010_08040201).AsByte() :
                                             Vector128.Create(0x01020408_10204080).AsByte();

                fixed (bool* destination = &boolArray[0])
                {
                    for (; (i + Vector128ByteCount * 2u) <= (uint)m_bitlength; i += Vector128ByteCount * 2u)
                    {
                        int bits = IntSpan[(int)(i / (uint)BitsPerInt32)];
                        Vector128<int> scalar = Vector128.CreateScalarUnsafe(bits);

                        Vector128<byte> shuffledLower = Ssse3.Shuffle(scalar.AsByte(), lowerShuffleMask);
                        Vector128<byte> extractedLower = Sse2.And(shuffledLower, bitMask128);
                        Vector128<byte> normalizedLower = Sse2.Min(extractedLower, ones);
                        Sse2.Store((byte*)destination + i, normalizedLower);

                        Vector128<byte> shuffledHigher = Ssse3.Shuffle(scalar.AsByte(), upperShuffleMask);
                        Vector128<byte> extractedHigher = Sse2.And(shuffledHigher, bitMask128);
                        Vector128<byte> normalizedHigher = Sse2.Min(extractedHigher, ones);
                        Sse2.Store((byte*)destination + i + Vector128<byte>.Count, normalizedHigher);
                    }
                }
            }
            else if (AdvSimd.IsSupported)
            {
                Vector128<byte> ones = Vector128.Create((byte)1);
                Vector128<byte> bitMask128 = BitConverter.IsLittleEndian ?
                                             Vector128.Create(0x80402010_08040201).AsByte() :
                                             Vector128.Create(0x01020408_10204080).AsByte();

                fixed (bool* destination = &boolArray[0])
                {
                    for (; (i + Vector128ByteCount * 2u) <= (uint)m_bitlength; i += Vector128ByteCount * 2u)
                    {
                        int bits = IntSpan[(int)(i / (uint)BitsPerInt32)];
                        // Same logic as SSSE3 path, except we do not have Shuffle instruction.
                        // (TableVectorLookup could be an alternative - dotnet/runtime#1277)
                        // Instead we use chained ZIP1/2 instructions:
                        // (A0 is the byte containing LSB, A3 is the byte containing MSB)
                        // bits (on Big endian)                 - A3 A2 A1 A0
                        // bits (Little endian) / Byte reversal - A0 A1 A2 A3
                        // v1 = Vector128.Create                - A0 A1 A2 A3 A0 A1 A2 A3 A0 A1 A2 A3 A0 A1 A2 A3
                        // v2 = ZipLow(v1, v1)                  - A0 A0 A1 A1 A2 A2 A3 A3 A0 A0 A1 A1 A2 A2 A3 A3
                        // v3 = ZipLow(v2, v2)                  - A0 A0 A0 A0 A1 A1 A1 A1 A2 A2 A2 A2 A3 A3 A3 A3
                        // shuffledLower = ZipLow(v3, v3)       - A0 A0 A0 A0 A0 A0 A0 A0 A1 A1 A1 A1 A1 A1 A1 A1
                        // shuffledHigher = ZipHigh(v3, v3)     - A2 A2 A2 A2 A2 A2 A2 A2 A3 A3 A3 A3 A3 A3 A3 A3
                        if (!BitConverter.IsLittleEndian)
                        {
                            bits = BinaryPrimitives.ReverseEndianness(bits);
                        }
                        Vector128<byte> vector = Vector128.Create(bits).AsByte();
                        vector = AdvSimd.Arm64.ZipLow(vector, vector);
                        vector = AdvSimd.Arm64.ZipLow(vector, vector);

                        Vector128<byte> shuffledLower = AdvSimd.Arm64.ZipLow(vector, vector);
                        Vector128<byte> extractedLower = AdvSimd.And(shuffledLower, bitMask128);
                        Vector128<byte> normalizedLower = AdvSimd.Min(extractedLower, ones);
                        AdvSimd.Store((byte*)destination + i, normalizedLower);

                        Vector128<byte> shuffledHigher = AdvSimd.Arm64.ZipHigh(vector, vector);
                        Vector128<byte> extractedHigher = AdvSimd.And(shuffledHigher, bitMask128);
                        Vector128<byte> normalizedHigher = AdvSimd.Min(extractedHigher, ones);
                        AdvSimd.Store((byte*)destination + i + Vector128<byte>.Count, normalizedHigher);
                    }
                }
            }
#endif

            LessThan32:
            for (; i < (uint)m_bitlength; i++)
            {
                int elementIndex = Div32Rem((int)i, out int extraBits);
                boolArray[(int)i] = ((IntSpan[elementIndex] >> extraBits) & 0x00000001) != 0;
            }
        }

        public bool TryFormat(Span<char> destination, out int charsWritten, ReadOnlySpan<char> format, IFormatProvider? provider)
        {
            if (!format.IsEmpty)
                throw new ArgumentException("format must empty", nameof(format));

            int len = 2 + m_bitlength;
            if (destination.Length < len)
            {
                charsWritten = 0;
                return false;
            }

            "0b".AsSpan().CopyTo(destination);
            for (int i = 0; i < m_bitlength; i++)
            {
                destination[2 + (m_bitlength - i) - 1] = Get(i) ? '1' : '0';
            }
            charsWritten = len;
            return true;
        }

        public string ToBinaryLiteral()
        {
            if (m_bitlength == 0)
                return String.Empty;

            return string.Create(2 + m_bitlength, this, static (chars, self) =>
            {
                var success = self.TryFormat(chars, out var _, default, default);
                Debug.Assert(success);
            });
        }


        public int PopCount()
        {
            if (m_bitlength <= BitsOfBackField)
            {
                return BitOperations.PopCount((ulong)m_backfield);
            }

            int count = 0;
            var span = AsInt32Span();
            for (var i = 0; i < span.Length; i++)
            {
                uint value = (i == span.Length - 1) ?
                    ((uint)(span[i] & ((1 << (m_bitlength & 0b11111)) - 1))) :
                    ((uint)span[i]);
                count += BitOperations.PopCount(value);
            }
            return Math.Min(count, m_bitlength);
        }

        //public ImmutableBitArray Slice(Range range) => throw new NotImplementedException();
        // public int LeadingZeroCount() => throw new NotImplementedException();
        // public int TrailingZeroCount() => throw new NotImplementedException();


        // XPerY=n means that n Xs can be stored in 1 Y.
        private const int BitsPerInt32 = 32;
        private const int BitsPerByte = 8;

        private const int BitShiftPerInt32 = 5;
        private const int BitShiftPerByte = 3;
        private const int BitShiftForBytesPerInt32 = 2;

        /// <summary>
        /// Used for conversion between different representations of bit array.
        /// Returns (n + (32 - 1)) / 32, rearranged to avoid arithmetic overflow.
        /// For example, in the bit to int case, the straightforward calc would
        /// be (n + 31) / 32, but that would cause overflow. So instead it's
        /// rearranged to ((n - 1) / 32) + 1.
        /// Due to sign extension, we don't need to special case for n == 0, if we use
        /// bitwise operations (since ((n - 1) >> 5) + 1 = 0).
        /// This doesn't hold true for ((n - 1) / 32) + 1, which equals 1.
        ///
        /// Usage:
        /// GetArrayLength(77): returns how many ints must be
        /// allocated to store 77 bits.
        /// </summary>
        /// <param name="n"></param>
        /// <returns>how many ints are required to store n bytes</returns>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static int GetInt32ArrayLengthFromBitLength(int n)
        {
            Debug.Assert(n >= 0);
            return (int)((uint)(n - 1 + (1 << BitShiftPerInt32)) >> BitShiftPerInt32);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static int GetInt32ArrayLengthFromByteLength(int n)
        {
            Debug.Assert(n >= 0);
            // Due to sign extension, we don't need to special case for n == 0, since ((n - 1) >> 2) + 1 = 0
            // This doesn't hold true for ((n - 1) / 4) + 1, which equals 1.
            return (int)((uint)(n - 1 + (1 << BitShiftForBytesPerInt32)) >> BitShiftForBytesPerInt32);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static int GetByteArrayLengthFromBitLength(int n)
        {
            Debug.Assert(n >= 0);
            // Due to sign extension, we don't need to special case for n == 0, since ((n - 1) >> 3) + 1 = 0
            // This doesn't hold true for ((n - 1) / 8) + 1, which equals 1.
            return (int)((uint)(n - 1 + (1 << BitShiftPerByte)) >> BitShiftPerByte);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static int Div32Rem(int number, out int remainder)
        {
            uint quotient = (uint)number / 32;
            remainder = number & (32 - 1);    // equivalent to number % 32, since 32 is a power of 2
            return (int)quotient;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static int Div4Rem(int number, out int remainder)
        {
            uint quotient = (uint)number / 4;
            remainder = number & (4 - 1);   // equivalent to number % 4, since 4 is a power of 2
            return (int)quotient;
        }

        private static void ThrowArgumentOutOfRangeException(int index)
        {
            throw new ArgumentOutOfRangeException(nameof(index), index, SR.ArgumentOutOfRange_Index);
        }

        public bool Equals(ImmutableBitArray other)
        {
            return m_bitlength == other.m_bitlength && IntSpan.SequenceEqual(other.IntSpan);
        }

        public override int GetHashCode()
        {
            return HashCode.Combine(m_bitlength, m_array?.Length ?? m_backfield.GetHashCode());
        }
        public override bool Equals(object? obj)
        {
            return obj is ImmutableBitArray other && Equals(other);
        }

        public static bool operator ==(ImmutableBitArray left, ImmutableBitArray right) => left.Equals(right);
        public static bool operator !=(ImmutableBitArray left, ImmutableBitArray right) => !(left == right);

        public IEnumerator<bool> GetEnumerator()
        {
            return new BitArrayEnumeratorSimple(this);
        }

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

        private sealed class BitArrayEnumeratorSimple : IEnumerator<bool>, ICloneable
        {
            private readonly ImmutableBitArray _bitArray;
            private int _index;
            private bool _currentElement;

            internal BitArrayEnumeratorSimple(ImmutableBitArray bitArray)
            {
                _bitArray = bitArray;
                _index = -1;
                _currentElement = default;
            }

            public object Clone() => MemberwiseClone();

            public bool MoveNext()
            {
                if (_index < (_bitArray.Length - 1))
                {
                    _index++;
                    _currentElement = _bitArray.Get(_index);
                    return true;
                }
                else
                {
                    _index = _bitArray.Length;
                }

                return false;
            }

            public bool Current
            {
                get
                {
                    if ((uint)_index >= (uint)_bitArray.Length)
                    {
                        throw GetInvalidOperationException(_index);
                    }

                    return _currentElement;
                }
            }

            object IEnumerator.Current => Current;

            public void Reset()
            {
                _index = -1;
            }

            private InvalidOperationException GetInvalidOperationException(int index)
            {
                if (index == -1)
                {
                    return new InvalidOperationException(SR.InvalidOperation_EnumNotStarted);
                }
                else
                {
                    Debug.Assert(index >= _bitArray.Length);
                    return new InvalidOperationException(SR.InvalidOperation_EnumEnded);
                }
            }

            public void Dispose()
            {
            }
        }
    }

    internal static class SR
    {
        public static string InvalidOperation_EnumEnded => nameof(InvalidOperation_EnumEnded);

        public static string InvalidOperation_EnumNotStarted => nameof(InvalidOperation_EnumNotStarted);
        public static string InvalidOperation_EnumFailedVersion => nameof(InvalidOperation_EnumFailedVersion);
        public static string ArgumentOutOfRange_Index => nameof(ArgumentOutOfRange_Index);
        public static string Arg_BitArrayTypeUnsupported => nameof(Arg_BitArrayTypeUnsupported);
        public static string Argument_InvalidOffLen => nameof(Argument_InvalidOffLen);
        public static string ArgumentOutOfRange_NeedNonNegNum => nameof(ArgumentOutOfRange_NeedNonNegNum);
        public static string Arg_ArrayLengthsDiffer => nameof(Arg_ArrayLengthsDiffer);

        public static string Argument_ArrayTooLarge => nameof(Argument_ArrayTooLarge);

        public static string Arg_RankMultiDimNotSupported => nameof(Arg_RankMultiDimNotSupported);

        internal static string Format(string argument_ArrayTooLarge, params object[] args)
        {
            return argument_ArrayTooLarge;
        }
    }
}
