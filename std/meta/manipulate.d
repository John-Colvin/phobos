module std.meta.manipulate;

import std.meta.pack;
import std.meta.algorithm;
import std.meta.seq;
import std.traits;

/**
 * Concatenates 2 $(D Pack)s to form a new $(D Pack) of equal or greater length
 */
template Chain(T ...)
    if(All!(isPack, Pack!T))
{
    alias Chain = Map!(Unpack, Pack!T);
}

unittest
{
//    pragma(msg, Chain!(Pack!(1,2,3), Pack!(4,5,6)));
    static assert(is(Chain!(Pack!(1,2,3), Pack!(4,5,6)) == Pack!(1,2,3,4,5,6)));
//    pragma(msg, Chain!(Pack!(1,2,3), Pack!()));
    static assert(is(Chain!(Pack!(1,2,3), Pack!()) == Pack!(1,2,3)));

    int a, b, c;
    alias Test = Pack!(a, b, c);
    alias Chained = Chain!(Pack!(a, b, c), Pack!(a, b, c));
    static assert(is(Chained == Pack!(a,b,c,a,b,c)));
    Chained.Index!(2) = 3;
    assert(c == 3);
}

/**
 * Get the first element of a $(D Pack)
 */
template Front(T)
    if(isPack!T)
{
    static if(__traits(compiles, { alias Front = T.Unpack[0]; }))
    {
	alias Front = T.Unpack[0];
    }
    else
    {
	enum Front = T.Unpack[0];
    }
}

unittest
{
    static assert(Front!(Pack!(1,2,3)) == 1);
    static assert(is(Front!(Pack!(int, long)) == int));
}

/**
 * Get the last element of a Pack.
 */
template Back(A)
    if(isPack!A)
{
    static if(__traits(compiles, { alias Back = A.Unpack[0]; }))
    {
	alias Back = A.Unpack[$-1];
    }
    else
    {
        enum Back = A.Unpack[$-1];
    }
}

unittest
{
    static assert(Back!(Pack!(1,2,3)) == 3);
    static assert(is(Back!(Pack!(int, long)) == long));
}

/**
 * Results in the given Pack minus it's head. Returns an empty Pack when given
 * an input length <= 1
 */
template Tail(A)
    if(isPack!A)
{
    static if(A.length == 0)
    {
        alias Tail = Pack!();
    }
    alias Tail = Slice!(A, 1, A.length);
}

unittest
{
    static assert(is(Tail!(Pack!(short, int, long)) == Pack!(int, long)));
}


/**
 * Reverses a given $(D Pack)
 */
template Retro(TList)
    if(isPack!TList)
{
//    pragma(msg, Retro);
    static if (TList.length <= 1)
    {
        alias Retro = TList;
    }
    else
    {
        alias Retro =
            Chain!(
                Retro!(Pack!(TList.Unpack[$/2 ..  $ ])),
                Retro!(Pack!(TList.Unpack[ 0  .. $/2])));
    }
}

///
unittest
{
    alias Types = Pack!(int, long, long, int, float);

    alias TL = Retro!(Types);
    static assert(is(TL == Pack!(float, int, long, long, int)));
}

/**
 * Evaluates to a new $(D Pack) containing each $(D n)th member of $(D P)
 */
template Stride(P, size_t n)
    if(isPack!P)
{
    static assert(n != 0, "n cannot be 0");
    static if(n == 1)
    {
	alias Stride = P;
    }
    else static if(n >= P.length)
    {
	alias Stride = Pack!(Front!P);
    }
    else
    {
	alias Stride = Pack!(Front!P,
			     Stride!(Slice!(P, n, P.length), n).Unpack);
    }
}
///
unittest
{
    static assert(is(Stride!(Pack!(1,2,3,4), 2) == Pack!(1,3)));
    static assert(is(Stride!(Pack!(int, short, 4, 3, 2, 1), 3)
		     == Pack!(int, 3)));
}

/**
 * Given a template argument list of $(D Pack)s, $(D RoundRobin) evalues to the 
 * first elements of each $(D Pack), followed by the second elements and so on. 
 * If the $(D Packs) are of unequal length, the missing elements are simply 
 * omitted. See $(XREF range, roundRobin)
 */
template RoundRobin(Packs ...)
    if(SeqAll!(isPack, Packs))
{
    static if(SeqAll!(hasLength!(Packs[0].length), Packs))
    {//All the same length
	alias RoundRobin = Map!(Unpack, Zip!(Packs));
    }
    else
    {//different lengths
	alias lengths = Map!(Length, Pack!Packs);
	enum shortest = MinPos!(Min, lengths);
	enum zlen = Index!(lengths, shortest);
	enum longestLen = MinPos!(Max, lengths);

	alias remaining = Seq!(Packs[0 .. shortest], Packs[shortest + 1 .. $]);
	alias remainingTruncated = Map!(Slice!zlen, Pack!remaining).Unpack;

	alias init = Map!(Unpack, Zip!(Packs));
	alias RoundRobin = Concat!(init, RoundRobin!remainingTruncated);
    }
}
///
unittest
{
    alias a = Pack!(1, 2, 3);
    alias b = Pack!(10, 20, 30, 40);
    alias r = RoundRobin!(a, b);
    static assert(is(r == Pack!(1, 10, 2, 20, 3, 30, 40)));
}


/**
 * Starting from $(D index), Radial evaluates to a $(D Pack) of alternate left
 * and right members of $(D P)
 */
template Radial(P, size_t index = P.length / 2)
    if(isPack!P)
{
    alias Radial = RoundRobin!(Retro!(Slice!(P, 0, index+1)),
			       Slice!(P, index+1, P.length));
}

/**
 * Evaluates to a $(D Pack) of the first $(D n) elements of $(D P)
 */
template Take(P, size_t n)
    if(isPack!P)
{
    alias Take = Slice!(P, 0, n);
}

/**
 * Evaluates to a $(D Pack) of the last $(D P.length - n) elements of $(D P)
 */
template Drop(P, size_t n)
    if(isPack!P)
{
    alias Drop = Slice!(P, n, P.length);
}

/**
 * Evaluates to a $(D Pack) of the first $(D P.length - n) elements of $(D P)
 */
template DropBack(P, size_t n)
    if(isPack!P)
{
    alias DropBack = Slice!(P, 0, P.length - n);
}


/**
 * Repeats A n times.
 *
 * If only a size is passed, Repeat results in a template that is pre-set to 
 * repeat it's arguments n times
 */
template Repeat(alias A, size_t n)
    if(!__traits(compiles, expectType!A)) //break any ambiguity
{
    static if(n == 0)
    {
        alias Repeat = Pack!();
    }
    else
    {
        alias Repeat = Pack!(A, Repeat!(A, n-1).Unpack);
    }
}
template Repeat(A, size_t n)
{
    static if(n == 0)
    {
        alias Repeat = Pack!();
    }
    else
    {
        alias Repeat = Pack!(A, Repeat!(A, n-1).Unpack);
    }
}

///
unittest
{
    static assert(is(Repeat!(4, 5) == Pack!(4,4,4,4,4)));
    static assert(is(Repeat!(Pack!(), 3) == Pack!(Pack!(), Pack!(), Pack!())));
}

//package for now
package template Repeat(size_t n)
{
    template Repeat(T ...)
    {
        alias Repeat = Repeat!(n, T);
    }
}

/**
 * Evaluates to a Pack containing the contents of the $(D Pack) $(D P) repeated
 * $(D n) times
 */
template Cycle(P, size_t n)
    if(isPack!P)
{
    static if(n == 0)
    {
        alias Cycle = Pack!();
    }
    else
    {
        alias Cycle = Chain!(P, Cycle!(P, n-1));
    }
}

///
unittest
{
    static assert(is(Cycle!(Pack!(int, uint), 2)
		     == Pack!(int, uint, int, uint)));
}

/**
 * Evaluates to $(D Pack!S) where $(D S) is a $(D Seq) such that 
 * $(D S[n] = F!(S[n - State.length .. n])). See $(XREF range, sequence).
 * The first $(D n) elements of $(D S) are initialized from $(D State).
 * The final length of $(D S) is equal to $(D length).
 */
template Sequence(alias F, size_t length, State ...)
{
    alias Sequence = SequenceImpl!(F, length, State.length, Pack!(State));
}

private template SequenceImpl(alias F, size_t length, size_t stateLength, State)
{
    static if(length == State.length)
    {
	alias SequenceImpl = State;
    }
    else
    {
	alias newState = Chain!(State, Pack!(F!(State[$ - stateLength .. $])));
	alias SequenceImpl = SequenceImpl!(F, length, stateLength, newState);
    }
}

/**
 * This template will generate a Seq of values over a range.
 * This is can particularly useful when a static $(D foreach) is desired.
 *
 * The range starts at $(D begin), and is increment by $(D step) until the 
 * value $(D end) has been reached. $(D begin) defaults to $(D 0), and $(D step)
 * defaults to $(D 1).
 *
 * See also $(XREF range,iota).
 *
 * Originally written by Monarch Dodra
*/
template Iota(alias end)
{
    alias E = typeof(end);
    alias Iota = Pack!(IotaImpl!(E, 0, end, 1));
}
///ditto
template Iota(alias begin, alias end)
{
    alias E = CommonType!(typeof(begin), typeof(end));
    alias Iota = Pack!(IotaImpl!(E, begin, end, 1));
}
///ditto
template Iota(alias begin, alias end, alias step)
{
    alias E = CommonType!(typeof(begin), typeof(end), typeof(step));
    alias Iota = Pack!(IotaImpl!(E, begin, end, step));
}

private template IotaImpl(E, E begin, E end, E step)
{
    static if (!isScalarType!E)
    {
        static assert(0, "Iota: parameters must be scalar types.");
    }
    else static if (step > 0 && begin + step >= end)
    {
        static if (begin < end)
            alias IotaImpl = Seq!begin;
        else
            alias IotaImpl = Seq!();
    }
    else static if (step < 0 && begin + step <= end)
    {
        static if (begin > end)
            alias IotaImpl = Seq!begin;
        else
            alias IotaImpl = Seq!();
    }
    else static if (begin == end)
    {
        alias IotaImpl = Seq!();
    }
    else static if (step)
    {
        enum newbeg = begin + step;
        enum mid1 = step + (end - newbeg) / 2;
        enum mid = begin + mid1 - (mid1 % step);
        alias IotaImpl = Seq!(.IotaImpl!(E, begin, mid, step),
			      .IotaImpl!(E, mid, end, step));
    }
    else
    {
        static assert(0, "step must be non-0 for begin != end");
    }
}

unittest
{
    static assert(Iota!(0).length == 0);

    int[] a;
    foreach (n; Iota!5.Unpack)
        a ~= n;
    assert(a == [0, 1, 2, 3, 4]);

    a.length = 0;
    foreach (n; Iota!(-5).Unpack)
        a ~= n;
    assert(a.length == 0);

    a.length = 0;
    foreach (n; Iota!(4, 7).Unpack)
        a ~= n;
    assert(a == [4, 5, 6]);

    a.length = 0;
    foreach (n; Iota!(-1, 4).Unpack)
        a ~= n;
    assert(a == [-1, 0, 1, 2, 3]);

    a.length = 0;
    foreach (n; Iota!(4, 2).Unpack)
        a ~= n;
    assert(a.length == 0);

    a.length = 0;
    foreach (n; Iota!(0, 10, 2).Unpack)
        a ~= n;
    assert(a == [0, 2, 4, 6, 8]);

    a.length = 0;
    foreach (n; Iota!(3, 15, 3).Unpack)
        a ~= n;
    assert(a == [3, 6, 9, 12]);

    a.length = 0;
    foreach (n; Iota!(15, 3, 1).Unpack)
        a ~= n;
    assert(a.length == 0);

    a.length = 0;
    foreach (n; Iota!(10, 0, -1).Unpack)
        a ~= n;
    assert(a == [10, 9, 8, 7, 6, 5, 4, 3, 2, 1]);

    a.length = 0;
    foreach (n; Iota!(15, 3, -2).Unpack)
        a ~= n;
    assert(a == [15, 13, 11, 9, 7, 5]);

    a.length = 0;
    foreach(n; Iota!(0, -5, -1).Unpack)
        a ~= n;
    assert(a == [0, -1, -2, -3, -4]);

    foreach_reverse(n; Iota!(-4, 1).Unpack)
    assert(a == [0, -1, -2, -3, -4]);

    static assert(!is(typeof( Iota!(15, 3, 0).Unpack ))); // stride = 0 statically
}

unittest
{
    auto foo1()
    {
        double[] ret;
        foreach(n; Iota!(0.5, 3).Unpack)
            ret ~= n;
        return ret;
    }
    auto foo2()
    {
        double[] ret;
        foreach(j, n; Seq!(Iota!(0, 1, 0.25).Unpack, 1))
            ret ~= n;
        return ret;
    }
    auto foo3()
    {
        double[] ret;
        foreach(j, n; Seq!(Iota!(1, 0, -0.25).Unpack, 0))
            ret ~= n;
        return ret;
    }
    auto foo4()
    {
        string ret;
        foreach(n; Iota!('a', 'g').Unpack)
            ret ~= n;
        return ret;
    }
    static assert(foo1() == [0.5, 1.5, 2.5]);
    static assert(foo2() == [0, 0.25, 0.5, 0.75, 1]);
    static assert(foo3() == [1, 0.75, 0.5, 0.25, 0]);
    static assert(foo4() == "abcdef");
}

/**
 * Evaluates to a $(D Pack) of the $(D n)th elements of each of $(D PoP),
 * where $(D PoP) is a $(D Pack) of $(D Pack)s.
 */
template Transversal(PoP, size_t n)
    if(isPack!PoP && All!(PoP, isPack))
{
    alias Transversal = Map!(Index!(n), PoP);
}

/**
 * Evaluates to the first element of each of $(D PoP),
 * where $(D PoP) is a $(D Pack) of $(D Pack)s.
 */
template FrontTransversal(PoP)
    if(isPack!PoP && All!(PoP, isPack))
{
    alias FrontTransversal = Map!(Front, PoP);
}


/**
 * Evaluates to $(D Source), reordered according to $(D Indices).
 */
template Indexed(Source, Indices)
    if(isPack!Source && isPack!Indices)
//should check if indices are valid type
{
    alias Indexed = Map!(Index!Source, Indices);
}


/**
 * Splits $(D Source) in to chunks of length $(D chunkSize). The final Pack
 * in the returned $(D Pack) of $(D Pack)s contains the $(Source.length % chunkSize)
 * remaining elements.
 */
template Chunks(Source, size_t chunkSize)
    if(isPack!Source)
{
    static if(chunkSize >= Source.length)
    {
	alias Chunks = Pack!(Source);
    }
    else
    {
	alias Chunks =
	    Pack!(Slice!(Source, 0, chunkSize),
		  Chunks!(Slice!(Source, chunkSize), chunkSize).Unpack);
    }
}

/**
 * Appends $(D T) to the $(D Pack) $(D Q).
 */
template Append(Q, T)
    if(isPack!Q)
{
    alias Append = Pack!(Q.Unpack, T);
}

//package for now
package alias Append(T) = PartialApply!(.Append, 1, T);

package alias AppendTo(Q) = PartialApply!(.Append, 0, Q);

/**
 * Prepends $(D T) to the $(D Pack) $(D Q).
 */
template Prepend(Q, T)
    if(isPack!T)
{
    alias Prepend = Pack!(T, Q.Unpack);
}

//package for now
package alias Prepend(T) = PartialApply!(.Prepend, 1, T);

package alias PrependTo(Q) = PartialApply!(.Prepend, 0, Q);

//Should be removed, identical to Chain
package template Concat(A, B)
    if(isPack!A && isPack!B)
{
    alias Concat = Pack!(A.Unpack, B.Unpack);
}

package template Concat(Packs ...)
    if(All!(isPack, Pack!Packs) && Packs.length > 2)
{
    alias Concat = Concat!(Packs[0], Concat!(Packs[1 .. $]));
}

//zip with stopping policy?

/**
 * Zip for $(D Pack)s. Results in a $(D Seq) containing a $(D Pack) of the first elements
 * of the passed $(D Pack)s, a $(D Pack) for the second elements etc.
 */
template Zip(Sets ...)
    if(SeqAll!(isPack, Sets))
{
    static if(Sets.length == 0)
    {
        alias Zip = Pack!();
    }
    else
    {        
        static if(SeqAny!(Empty, Sets))
        {
            alias Zip = Repeat!(Pack!(), Sets.length); //questionable
        }
        else static if(SeqAny!(hasLength!(1), Sets))
        {
            alias Zip = Pack!(Map!(Front, Pack!Sets));
        }
        else
        {
            alias Zip = Pack!(Map!(Front, Pack!Sets),
			      Zip!(Map!(Tail, Pack!Sets).Unpack).Unpack);
        }
    }
}

unittest
{
    static assert(is(Zip!(Pack!(), Pack!()) == Pack!(Pack!(), Pack!())));

    static assert(is(Zip!(Pack!(short, int, long), Pack!(2,4,8))
		     == Pack!(Pack!(short, 2), Pack!(int, 4), Pack!(long, 8))));
}
