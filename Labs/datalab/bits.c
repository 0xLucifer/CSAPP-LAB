/*
	C语言中运算符共有6种：
	1、算数运算符 - Arithmetic	Operators
	2、关系运算符 - Relational	Operators
	3、逻辑运算符 - Logical		Operators
	4、位级运算符 - BitWise		Operators
	5、赋值运算符 - Assignment	Operators
	6、杂项运算符 - Misc		Operators
	做本题之前，需要对上面的概念了解
	具体做题要求，见原bits.c文件
*/


/*
 *   01/13
 *   bitXor - x^y using only ~ and &
 *   Example:
 *       bitXor(4, 5) = 1
 *   Legal ops: ~ &
 *   Max ops: 14
 *   Rating: 1
 */
int bitXor(int x, int y)
{
	return ~(~(x & ~y) & ~(~x & y));
}


/*
 *   02/13
 *   tmin - return minimum two's complement integer
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 4
 *   Rating: 1
 */
int tmin(void)
{
 	return 1 << 31;
}


/*
 *   03/13
 *   isTmax - returns 1 if x is the maximum, two's complement number, and 0 otherwise
 *   Legal ops: ! ~ & ^ | +
 *   Max ops: 10
 *   Rating: 1
 */
int isTmax(int x)
{
	// tmin + tmax + 1 == 0
	return !(~((x + 1) + x) | !(x + 1));
}


/*
 *   04/13
 *   allOddBits - return 1 if all odd-numbered bits in word set to 1
 *   where bits are numbered from 0 (least significant) to 31 (most significant)
 *   Examples
 *       allOddBits(0xFFFFFFFD) = 0
 *       allOddBits(0xAAAAAAAA) = 1
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 12
 *   Rating: 2
 */
int allOddBits(int x)
{
	// 0x1010...&x == x
	int tmp = (0xAA << 24) + (0xAA << 16) + (0xAA << 8) + 0xAA;
	return !((tmp & x) ^ tmp);
}


/*
 *   05/13
 *   negate - return -x
 *   Example:
 *       negate(1) = -1.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 5
 *   Rating: 2
 */
int negate(int x)
{
	return ~x + 1;
}


/*
 *   06/13
 *   isAsciiDigit - return 1 if 0x30 <= x <= 0x39 (ASCII codes for characters '0' to '9')
 *   Example:
 *       isAsciiDigit(0x35) = 1.
 *       isAsciiDigit(0x3a) = 0.
 *       isAsciiDigit(0x05) = 0.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 15
 *   Rating: 3
 */
int isAsciiDigit(int x)
{
	/* (x - 0x30 >= 0) && (0x39 - x) >=0 */
	int NEG = 1 << 31;
	return !((x + ~0x30 + 1) & NEG) & !((0x39 + ~x + 1) & NEG);
}
/*
 *   07/13
 *   conditional - same as x ? y : z
 *   Example:
 *       conditional(2,4,5) = 4
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 16
 *   Rating: 3
 */
int conditional(int x, int y, int z)
{
	int tmp = ~(!!x) + 1;
	return (tmp & y) | (~tmp & z);
}


/*
 *   08/13
 *   isLessOrEqual - if x <= y  then return 1, else return 0
 *   Example:
 *       isLessOrEqual(4,5) = 1.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 24
 *   Rating: 3
 */
int isLessOrEqual(int x, int y)
{
	// First check signBit
	int signX = x >> 31;
	int signY = y >> 31;
	return (signX & !signY) | (!(signX ^ signY) & !((y + ~x + 1) >> 31));
}


/*
 *   09/13
 *   logicalNeg - implement the ! operator, using all of the legal operators except !
 *   Examples:
 *       logicalNeg(3) = 0
 *       logicalNeg(0) = 1
 *   Legal ops: ~ & ^ | + << >>
 *   Max ops: 12
 *   Rating: 4
 */
int logicalNeg(int x)
{
	return ((x | (~x + 1)) >> 31) + 1;
}


/*
 *   10/13
 *   howManyBits - return the minimum number of bits required to represent x in two's complement
 *   Examples:
 *       howManyBits(12) = 5
 *       howManyBits(298) = 10
 *       howManyBits(-5) = 4
 *       howManyBits(0)  = 1
 *       howManyBits(-1) = 1
 *       howManyBits(0x80000000) = 32
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 90
 *   Rating: 4
 */
int howManyBits(int x)
{
	int sign, b1, b2, b4, b8, b16;
	sign = (x >> 31);
	x = (sign & ~x) | (~sign & x);
	b16 = !!(x >> 16) << 4;
	x = x >> b16;
	b8 = !!(x >> 8) << 3;
	x = x >> b8;
	b4 = !!(x >> 4) << 2;
	x = x >> b4;
	b2 = !!(x >> 2) << 1;
	x = x >> b2;
	b1 = !!(x >> 1);
	x = x >> b1;
	return b16 + b8 + b4 + b2 + b1 + x + 1;
}


/*
 *   11/13
 *   floatScale2 - Return bit-level equivalent of expression 2*f for
 *   floating point argument f.
 *   Both the argument and result are passed as unsigned int's, but
 *   they are to be interpreted as the bit-level representation of
 *   single-precision floating point values.
 *   When argument is NaN, return argument
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Max ops: 30
 *   Rating: 4
 */
unsigned floatScale2(unsigned uf)
{
	int e    = (uf >> 23) & 0xff;
	int sign = uf & (0x1 << 31);
	int M    = (uf << 9) >> 9;
	if(M == 0 && e == 0)
	{
		return uf; // 0
	}
	if(e == 0x0)
	{
		return (uf << 1) | sign;
	}
	if(e == 0xff)
	{
		return uf; // NaN
	}
	e++;
	if(e == 0xff && M > 0)
	{
		return uf;
	}
	return sign | (e << 23) | M;
}


/*
 *   12/13
 *   floatFloat2Int - Return bit-level equivalent of expression (int) f
 *   for floating point argument f.
 *   Argument is passed as unsigned int, but
 *   it is to be interpreted as the bit-level representation of a
 *   single-precision floating point value.
 *   Anything out of range (including NaN and infinity) should return
 *   0x80000000u.
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Max ops: 30
 *   Rating: 4
 */
int floatFloat2Int(unsigned uf)
{
	int e = ((uf >> 23) & 0xff)-127;
	int sign = uf >> 31;
	int M = (uf&0x007fffff)|0x00800000;
	if(!(uf&0x7fffffff))
	{
		return 0; // 0
	}
	if(e < 0)
	{
		return 0; // 0.***
	}
	if(e > 31)
	{
		return 0x80000000; // overflow
	}
	if(!(uf & 0x7fffffff))
	{
		return 0; // 0
	}
	if(e > 23)
	{
		M <<= (e - 23);
	}
	else
	{
		M >>= (23 - e);
	}
	if(!((M >> 31) ^ sign)) // +
	{
		return M;
	}
	else
	{
		if(M >> 31) // overflow
		{
			return 0x80000000;
		}
	}
	return ~M + 1; // -
}


/*
 *   13/13
 *   floatPower2 - Return bit-level equivalent of the expression 2.0^x
 *   (2.0 raised to the power x) for any 32-bit integer x.
 *
 *   The unsigned value that is returned should have the identical bit
 *   representation as the single-precision floating-point number 2.0^x.
 *   If the result is too small to be represented as a denorm, return
 *   0. If too large, return +INF.
 *
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. Also if, while
 *   Max ops: 30
 *   Rating: 4
 */
unsigned floatPower2(int x)
{
	int INF = 0xff<<23;
	int exp = x + 127;
	if(exp <= 0)
	{
		return 0;
	}
	if(exp >= 255)
	{
		return INF;
	}
	return exp << 23;
}

