// Written in the D programming language.

/**
   This module contains the definition of the $(D Pack) type, an encapsulated collection of template parameter arguments.

   Authors: John L Colvin and monarch dodra (REAL NAME NEEDED??)

   License: $(WEB www.boost.org/LICENSE_1_0.txt, Boost License 1.0)

   Source: $(PHOBOSSRC std/meta/_pack.d)
 */

module std.meta.pack;

import std.meta.algorithm;
import std.meta.seq;
import std.meta.functional;
import std.meta.manipulate;
import std.traits;


/**
 * A mixin template to inject the definition of $(D Pack) in to a scope. Using this
 * will locally expand dot notation instantiation for Packs to symbols in said
 * scope.
 */
mixin template PackDef()
{
struct Pack(T...)
{
    private alias This = typeof(this);

    alias Unpack = T;

    enum length = T.length; //lowercase for familiarity

    @disable this();

    /*
     * UFCS for Packs.
     * takes care of all first argument functions
     * only works with templates visible in the scope of the definition
     * of pack
     */
    //if there was such a thing as a compilation context default
    //parameter we could import from / compile using, this would be better
    template opDispatch(string s)
    {
	mixin("alias opDispatch = PartialApply!(." ~ s ~ ", 0, typeof(this));");
    }

    //alias asArg(uint argIndex) = .asArg!(argIndex, typeof(this));
} //end of Pack struct
}

//adds Pack to the current scope
mixin PackDef!();

unittest
{
    alias W = Pack!(5,3,4);
    static assert(W.Index!(2) == 4);
//    static assert(is(asArg!(1, W).Map!(isPack) == Pack!(false, false, false)));
}

version(StdDdoc)
{
    /**
     * Confines a Seq within a struct. The result is simply a type: Access to the
     * underlying Seq is done using $(D Unpack).
     */
    struct Pack(T ...)
    {
        /// The unpacked version of the $(D Pack). See $(XREF meta_seq, Seq)
        alias Unpack = T;

        /// The length of the $(D Pack).
        enum length = T.length; //lowercase for familiarity
    }
}


/++
 + asArg returns a type that positions $(D T) in argument position $(D argIndex)
 + in any template $(D Templ) given as $(D asArg!(/*...*/).Templ!(/*...*/)) e.g.
 + $(D asArg!(1, Pack!(1, Pack!2, 3)).Map!isPack
 + //evaluates to Pack!(False, True, False))
 +/
struct asArg(size_t argIndex, T ...)
    if(T.length == 1)
{
    template opDispatch(string s)
    {
	mixin("alias opDispatch = PartialApply!(." ~ s ~ ", " ~ argIndex.stringof ~ ", T);");
    }
    @disable this();
}


/**
 * Results in the length of any compile-time entity that defines the field
 * length
 */
enum Length(P) = P.length;

/**
 * Check is the passed set of parameters is an instantiation of $(D Pack).
 *
 * Note:
 * This is a deliberatly permissive template: You can pass it absolutely
 * anything (that is itself valid) without error, it will simply return false
 * unless there is a single $(D Pack) argument only.
 */
template isPack(TList ...)
{
    static if(TList.length == 1 &&
	      is(Pack!(TList[0].Unpack) == TList[0]))
    {
	enum isPack = true;
    }
    else
    {
	enum isPack = false;
    }
}

unittest
{
    alias a = Pack!(int, 1);
    static assert(isPack!a);
    alias b = Seq!(int, 1);
    static assert(!isPack!b);

    static assert(!isPack!(isPack));
}

/**
 * Template accessor for Pack.Unpack
 */
template Unpack(A)
    if(A.isPack!())
{
    alias Unpack = A.Unpack;
}
///
unittest
{
    static assert(Unpack!(Pack!(1,2)) == Seq!(1,2));
}

/**
 * Checks if a given Pack is empty
 */
template Empty(T)
    if(isPack!T)
{
    static if(T.length == 0)
    {
	enum Empty = true;
    }
    else
    {   
	enum Empty = false;
    }
}
///
unittest
{
    static assert(Empty!(Pack!()));
    static assert(!Empty!(Pack!1));
}

/**
 * Checks if the given pack $(D T) has length $(D len)
 */
template hasLength(size_t len, T)
    if(isPack!T)
{
    static if(T.length == len)
    {
	enum hasLength = true;
    }
    else
    {   
	enum hasLength = false;
    }
}
///
unittest
{
    static assert(hasLength!(2, Pack!(0,1)));
}

// package for now
package alias hasLength(size_t len) = PartialApply!(.hasLength, 0, len);
///
unittest
{
    alias hl3 = hasLength!3;
    alias P = Pack!(1,3,5);
    static assert(hl3!P);
}

/**
 * Returns a slice of the Pack $(D P) from $(D i0) to $(D i1 - 1) inclusive.
 * $(D P) and $(D i1) are optional. 
 */
template Slice(P, size_t i0, size_t i1)
    if(isPack!P)
{
    alias Slice = Pack!(P.Unpack[i0 .. i1]);
}

//package for now
package alias Slice(P, size_t i0) = .Slice!(P, i0, P.length);

package alias Slice(size_t i0, size_t i1) = PartialApply!(.Slice, 1, i0, i1);

package alias Slice(size_t i0) = PartialApply!(.Slice, 1, i0);

/**
 * Evaluates to the $(D i)th element of $(D P) where $(D P) is a $(D Pack)
 */
template Index(P, size_t i)
    if(isPack!P)
{
    alias Index = Alias!(P.Unpack[i]);
}

// package for now
package alias Index(size_t i) = PartialApply!(.Index, 1, i);

package alias Index(P) = PartialApply!(.Index, 0, P);

