#! /usr/bin/jsc

"use strict"

var console = {
    log: function (...rest) { print(rest) }
}

function getline() {   // readln gets
    let l = readline();
    if (l) return l;
    quit(); }

// BEGIN
let TR_STANDALONE = 1;
let harvest = 0;
function mk_solver() {
/*
 A Succinct Trie for Javascript   https://www.hanovsolutions.com/trie/

 By Steve Hanov
 Released to the public domain.

 This file contains functions for creating a succinctly encoded trie structure
 from a list of words. The trie is encoded to a succinct bit string using the
 method of Jacobson (1989). The bitstring is then encoded using BASE-64. 
 
 The resulting trie does not have to be decoded to be used. This file also
 contains functions for looking up a word in the BASE-64 encoded data, in
 O(mlogn) time, where m is the number of letters in the target word, and n is
 the number of nodes in the trie.

 Objects for encoding:
 TrieNode
 Trie
 BitWriter
 RankDirectory.Create (just this method of the class)

 Objects for decoding:
 BitString
 FrozenNode
 FrozenTrie
 RankDirectory

 QUICK USAGE:

 Suppose we let data be some output of the demo encoder:

 var data = {
    "nodeCount": 37,
    "directory": "BMIg",
    "trie": "v2qqqqqqqpIUn4A5JZyBZ4ggCKh55ZZgBA5ZZd5vIEl1wx8g8A"
 };

 var frozenTrie = new FrozenTrie( Data.trie, Data.directory, Data.nodeCount);

 alert( frozenTrie.lookup( "hello" ) ); // outputs true
 alert( frozenTrie.lookup( "kwijibo" ) ); // outputs false

*/   

// Configure the bit writing and reading functions to work natively in BASE-64 
// encoding. That way, we don't have to convert back and forth to bytes.

let Game;
Game = "qwerasdfzxcvtegb";
Game = "eyleseeaovtiitqg";
Game = "twstnksijeeltswz";
let debugString = "";
let callsToSelect = 0;	// profiling
//let hist = [];  // profiling
let Memoization = [];
load("enctrie.js");	// Before, this load() defined "encDir" string
let encDir = '';	// Change to use encAbstract deprecates the directory
var BASE64 =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

/**
    The width of each unit of the encoding, in bits. Here we use 6, for base-64
    encoding.  If this W changes, need to also change ORD(), CHR() and BitString.MaskTop
    [update: use 7 bits so each encoding is a single ASCII (7-bit) character]
 */
const W = 7;  

function getMemo() { return Memoization }
function getDS() { return debugString }
function setGame(g) { Game = g }

/**
    Returns the character unit that represents the given value.  If this were
    binary data, we would simply return id.
 */
function CHR(id) 
{
    return String.fromCharCode(id);	// W=7
    return BASE64[id];			// W=6
}

/** 
    Returns the decimal value of the given character unit.
 */
var BASE64_CACHE = {"A" : 0, "B" : 1, "C" : 2, "D" : 3, "E" : 4, "F" : 5, "G" :
    6, "H" : 7, "I" : 8, "J" : 9, "K" : 10, "L" : 11, "M" : 12, "N" : 13, "O" :
    14, "P" : 15, "Q" : 16, "R" : 17, "S" : 18, "T" : 19, "U" : 20, "V" :
    21, "W" : 22, "X" : 23, "Y" : 24, "Z" : 25, "a" : 26, "b" : 27, "c" :
    28, "d" : 29, "e" : 30, "f" : 31, "g" : 32, "h" : 33, "i" : 34, "j" :
    35, "k" : 36, "l" : 37, "m" : 38, "n" : 39, "o" : 40, "p" : 41, "q" :
    42, "r" : 43, "s" : 44, "t" : 45, "u" : 46, "v" : 47, "w" : 48, "x" :
    49, "y" : 50, "z" : 51, "0" : 52, "1" : 53, "2" : 54, "3" : 55, "4" :
    56, "5" : 57, "6" : 58, "7" : 59, "8" : 60, "9" : 61, "-" : 62, "_" :
    63};

function ORD(ch) 
{
    // Used to be: (see below)
    return ch.charCodeAt(0);  // use 7-bit ASCII codes directly (one-for-one)

    // Used to be: return BASE64.indexOf(ch);
    return BASE64_CACHE[ch];  // W=6
}

/**
    Fixed values for the L1 and L2 table sizes in the Rank Directory
*/
let L1, L2;
L2 = 32;
L2 = 64;
L1 = 4*L2;
L1 = 32;

/**
    The BitWriter will create a stream of bytes, letting you write a certain
    number of bits at a time. This is part of the encoder, so it is not
    optimized for memory or speed.
*/
function BitWriter()
{
    this.init();
}

BitWriter.prototype = 
{
    init: function() {
        this.bits = [];
    },

    /**
        Write some data to the bit string. The number of bits must be 32 or
        fewer.
    */
    write: function( data, numBits ) {
        for( var i = numBits - 1; i >= 0; i-- ) {
            if ( data & ( 1 << i ) ) {
                this.bits.push(1);
            } else {
                this.bits.push(0);
            }
        }
    },

    put7Abstract: function(id) {
	let countSoFar = 0;
	let offset = 0;

	console.log(`@ ${id}`);
        for (let j = 0; j < this.bits.length; ++j) {
	    if (this.bits[j]) {
	        ++countSoFar;   // global count of # of bits=1 since the beginning
		++offset;
	    }
	    if (0 === j % 128) {
	        // Output 3 ASCII character # representing 21 bits of the integer "countSoFar"
		console.log((countSoFar >>14) & 0b1111111);
		console.log((countSoFar >> 7) & 0b1111111);
		console.log((countSoFar >> 0) & 0b1111111);
		offset = 0;
	    }
	    else if (0 === j % 32) {
	        // Output 1 ASCII character # representing the 7 bits of the integer "offset"
		console.log(offset);
	    }
	}
	console.log("@ trailer");
    },

    put7Data: function(id) {   // Bit Writer->put7Data to console the 7-bit ASCII codes
        let b = 0;
	let i = 0;

	console.log(`@ ${id}`);
        for (let j = 0; j < this.bits.length; ++j) {
	    b = (b << 1) | this.bits[j];
	    if ( ++i === W ) {
	        console.log(b);
		i = b = 0;
	    }
	}
	if (i) {
	    console.log(b << (W-i));  // pad with 0s if needed
	}
	console.log("@ trailer");
    },
    /**
        Return an encoded string representation.
        [old] Return the base64 representation of the this.bits array of 1s & 0s.
    */
    getData: function() {   // Bit Writer->getData
        var chars = [];
        var b = 0;
        var i = 0;

        for ( let j = 0; j < this.bits.length; j++ ) {
            b = ( b << 1 ) | this.bits[j];
            i += 1;
            if ( i === W ) {
                chars.push( CHR(b) );
                i = b = 0;
            }
        }
        if ( i ) {
            chars.push( CHR(b << ( W - i )) );  // pad with 0s if needed
        }
        return chars.join("");
    },

    /**
        Returns the bits as a human readable binary string for debug
     */
    getDebugString: function(group) {
        var chars = [];
        var i = 0;
        
        for( var j = 0; j < this.bits.length; j++ ) {
            chars.push( "" + this.bits[j] );
            i++;
            if ( i === group ) {
                chars.push( ' ' );
                i = 0;
            }
        }
        return chars.join("");
    },
};  // BitWriter

/**
    Given a string of data (eg, in BASE-64), the BitString class supports
    reading or counting a number of bits from an arbitrary position in the
    string.
*/
function BitString( str )
{
    this.init( str );
}

BitString.MaskTop = [ 
    /* W=6            0x3f, 0x1f, 0x0f, 0x07, 0x03, 0x01, 0x00    /* W dependency */
    /* W=7 */   0x7f, 0x3f, 0x1f, 0x0f, 0x07, 0x03, 0x01, 0x00    /* W dependency */
];

BitString.BitsInByte = [ 
    0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3, 3, 4, 2,
    3, 3, 4, 3, 4, 4, 5, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3,
    3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3,
    4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 2, 3, 3, 4,
    3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5,
    6, 6, 7, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4,
    4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5,
    6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 2, 3, 3, 4, 3, 4, 4, 5,
    3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 3,
    4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 4, 5, 5, 6, 5, 6, 6, 7, 5, 6,
    6, 7, 6, 7, 7, 8 
];

BitString.prototype = {
    init: function( str ) {
        this.bytes = str;
        this.length = this.bytes.length * W;
    },

    /**
      Returns the internal string of bytes
    */
    getData: function() {
        return this.bytes;
    },

    /**
        Returns a decimal number, consisting of a certain number, n, of bits
        starting at a certain position, p.
     */
    get: function( p, n ) {

        // case 1: bits lie within the given byte
        if ( ( p % W ) + n <= W ) {
            return ( ORD( this.bytes[ p / W | 0 ] ) & BitString.MaskTop[ p % W ] ) >> 
                ( W - p % W - n );

        // case 2: bits lie incompletely in the given byte
        } else {
            var result = ( ORD( this.bytes[ p / W | 0 ] ) & 
                BitString.MaskTop[ p % W ] );

            var l = W - p % W;
            p += l;
            n -= l;

            while ( n >= W ) {
                result = (result << W) | ORD( this.bytes[ p / W | 0 ] );
                p += W;
                n -= W;
            }

            if ( n > 0 ) {
                result = (result << n) | ( ORD( this.bytes[ p / W | 0 ] ) >> 
                    ( W - n ) );
            }
            return result;
        }
    },

    /**
        Counts the number of bits set to 1 starting at position p and
        ending at position p + n
     */
    count: function( p, n ) {

        var count = 0;
        while( n >= 8 ) {
            count += BitString.BitsInByte[ this.get( p, 8 ) ];
            p += 8;
            n -= 8;
        }
        return count + BitString.BitsInByte[ this.get( p, n ) ];
    },

    /**
        Returns the number of bits set to 1 up to and including position x.
        This is the slow implementation used for testing.
    */
    rankSlowDebug: function( x ) {
        var rank = 0;
        for( var i = 0; i <= x; i++ ) {
            if ( this.get(i, 1) ) {
                rank++;
            }
        }
        return rank;
    }
};// BitString.prototype

/**
    The rank directory allows you to build an index to quickly compute the
    rank() and select() functions.  The index can itself be encoded as a binary
    string.
 */
function RankDirectory( directoryData, bitData, numBits, l1Size, l2Size )
{
    this.init(directoryData, bitData, numBits, l1Size, l2Size);
}

/**
    Used to build a rank directory from the given input string.

    @param data A javascript string containing the data, as readable using the
    BitString object.

    @param numBits The number of bits to index.
    
    @param l1Size The number of bits that each entry in the Level 1 table
    summarizes.  This should be a multiple of l2Size.

    @param l2Size The number of bits that each entry in the Level 2 table
    summarizes.
 */
RankDirectory.Create = function( data, numBits, l1Size, l2Size ) {
    var bits = new BitString( data );
    var p = 0;
    var i = 0;
    var count1 = 0, count2 = 0;
    var l1bits = Math.ceil( Math.log( numBits ) / Math.log(2) );
    var l2bits = Math.ceil( Math.log( l1Size ) / Math.log(2) );

    //console.log("numBits/l1/l2bits", numBits,l1bits,l2bits);  // debugging

    var directory = new BitWriter();

    while( p + l2Size <= numBits ) {
        count2 += bits.count( p, l2Size );
        i += l2Size;
        p += l2Size;
        if ( i === l1Size ) {
            count1 += count2;
            directory.write( count1, l1bits );
            count2 = 0;
            i = 0;
        }
	else {
            directory.write( count2, l2bits );
        }
    }
    //if (harvest) directory.put7Data("encDir");  // abstract replaces directory
    return new RankDirectory( directory.getData(), data, numBits, l1Size, l2Size );
};  // RankDirectory.Create


RankDirectory.prototype = {

    init: function( directoryData, bitData, numBits, l1Size, l2Size ) {
        this.directory = new BitString( '' );
	this.abstract = directoryData;
        this.data = new BitString( bitData );
        this.l1Size = l1Size;
        this.l2Size = l2Size;
        this.l1Bits = Math.ceil( Math.log( numBits ) / Math.log( 2 ) );
        this.l2Bits = Math.ceil( Math.log( l1Size ) / Math.log( 2 ) );
        this.sectionBits = (l1Size / l2Size - 1) * this.l2Bits + this.l1Bits;
        this.numBits = numBits;
    },

    /**
        Returns the string representation of the directory.
     */
    getData: function() {
        return this.directory.getData();
    },

    /**
      Returns the number of 1 or 0 bits (depending on the "which" parameter)
      up to and including position x.
      */
    rank: function( which, x ) {
        let csf, offset;

        if ( which === 0 ) {
            return x - this.rank( 1, x ) + 1;
        }

	let q1 = Math.floor(x / 128);
	let r1 = x % 128;
	let q2 = Math.floor(r1 / 32);
	let r2 = r1 % 32;

	let csfIndex = q1*6;
	let c2 = this.abstract.charCodeAt(csfIndex+0);
	let c1 = this.abstract.charCodeAt(csfIndex+1);
	let c0 = this.abstract.charCodeAt(csfIndex+2);
	//console.log("c2/c1/c0", c2,c1,c0);  //debugging

	csf = c2*16384 + c1*128 + c0;

	offset = (0===q2) ?  0 :  this.abstract.charCodeAt(q2 + (csfIndex+2));

	let start = 1 + q1*128 + q2*32;
	let count =  this.data.count(start, r2);

	let sum = csf + offset + count;
	//console.log(`rank( ${x} ) ${csf}+${offset}+${count}=${sum}`);  // debugging
	//console.log("slowDebug(x)", x, this.data.rankSlowDebug(x));  // debugging
	return sum;
    },

    /**
      Returns the position of the y'th 0 or 1 bit, depending on the "which"
      parameter.
      */
    select: function( which, y ) {
        var high = this.numBits;
        var low = -1;
        var val = -1;

	++callsToSelect;  // profiling: log the # of times this binary search runs

        while ( high - low > 1 ) {
            var probe = (high + low) / 2 | 0;
            var r = this.rank( which, probe );

            if ( r === y ) {
                // We have to continue searching after we have found it,
                // because we want the _first_ occurrence.
                val = probe;
                high = probe;
            } else if ( r < y ) {
                low = probe;
            } else {
                high = probe;
            }
        }
        return val;
    }
};

/**
  A Trie node, for use in building the encoding trie. This is not needed for
  the decoder.
  */
function TrieNode( letter )
{
    this.letter = letter;
    this.final = false;
    this.children = [];
}

function Trie()
{
    this.init();
}

Trie.prototype = {
    init: function() {
        this.previousWord = "";
        this.root = new TrieNode(' ');
        this.cache = [ this.root ];
        this.nodeCount = 1;
    },

    /**
      Returns the number of nodes in the trie
     */
    getNodeCount: function() {
        return this.nodeCount;
    },

    /**
      Inserts a word into the trie.  This function is fastest if the words are
      inserted in alphabetical order.
     */
    insert: function( word ) {      

        var commonPrefix = 0;
        for(let i = 0; i < Math.min(word.length, this.previousWord.length); i++ ) {
            if ( word[i] !== this.previousWord[i] ) { break; }
            commonPrefix += 1;
        }

        this.cache.length = commonPrefix + 1;
        var node = this.cache[ this.cache.length - 1 ];

        for( let i = commonPrefix; i < word.length; i++ ) {
            var next = new TrieNode( word[i] );
            this.nodeCount++;
            node.children.push( next );
            this.cache.push( next );
            node = next;
        }

        node.final = true;
        this.previousWord = word;
    },

    /**
      Invoke the supplied function for every node in trie,
      traversing the trie in level (breadth-first) order.
      */
    traverseTree: function( fn )   // was apply(), which is a method claimed by JavaScript
    {
        var level = [ this.root ];
        while( level.length > 0 ) {
            var node = level.shift();
            for( var i = 0; i < node.children.length; i++ ) {
                level.push( node.children[i] );
            }
            fn( node );
        }
    },

    /**
      Encode the trie and all of its nodes.  Returns a string representing the
      encoded data.
      */
    encode: function()
    {
        // Write the unary encoding of the tree in level order.
        var bits = new BitWriter();
        bits.write( 0x02, 2 );  // This is the "super" node
        this.traverseTree( function( node ) {
            for( var i = 0; i < node.children.length; i++ ) {
                bits.write( 1, 1 );
            }
            bits.write( 0, 1 );
        });

	// Write the data for each node, using 6 bits per node.
	// In bit[5], store the "final" flag.  The remaining five
	// lower bits encode a lowercase letter of the latin alphabet.
	//
	if (harvest) console.log("@ encLetter");
        var a = ("a").charCodeAt(0);
        this.traverseTree( function( node ) {
            var value = node.letter.charCodeAt(0) - a;

	    // The root node has an associated "letter" of ascii space,
	    // and ' ' - 'a' = -65.  That is why the root node appears
	    // in the encoded bitsequence as six 1s (0x3f)
	    //
	    //console.log("encode 5", value);  // debugging

            if ( node.final ) {
                value |= 0x20;
            }

            //bits.write( value, 6 );
	    if (harvest) console.log(value);
        });
	if (harvest) console.log("@ trailer");

        debugString = bits.getDebugString(8);  // arg[0]: number of bits printed between spaces
	if (harvest) bits.put7Data("encTrie");
	if (harvest) bits.put7Abstract("encAbstract");
        return bits.getData();
    }// encode()
};

/**
  This class is used for traversing the succinctly encoded trie.
  */
function FrozenNode( trie, index, letter, final, firstChild, childCount )
{
    this.trie = trie;
    this.index = index;
    this.letter = letter;
    this.final = final;
    this.cached = null;		// becomes non-null once the cache is initialized
    this.firstChild = firstChild;
    this.childCount = childCount;
}

FrozenNode.prototype = {
    cachedChildByLetter: function(letter) {
        return this.cached[letter];
    },

    cacheTheChildren: function() {
        let child;   // a FrozenNode

        this.cached = {};
	for (let idx=0; idx < this.getChildCount(); ++idx) {
	    child = this.getChild(idx);
	    this.cached[child.letter] = child;
	}
    },

    /**
      Returns the number of children.
      */
    getChildCount: function()
    {
        return this.childCount;
    },

    /**
      Returns the FrozenNode for the given child.

      @param index The 0-based index of the child of this node. For example, if
      the node has 5 children, and you wanted the 0th one, pass in 0.
    */
    getChild: function(index) 
    {
        return this.trie.getNodeByIndex( this.firstChild + index );
    }
};

/**
    The Frozen Trie is used for looking up words in the encoded trie.

    @param data A string representing the encoded trie.

    @param directoryData A string representing the RankDirectory. The global L1
    and L2 constants are used to determine the L1Size and L2size.

    @param nodeCount The number of nodes in the trie.
  */
function FrozenTrie( data, directoryData, nodeCount, letterData, abstractData )
{
    this.init( data, directoryData, nodeCount, letterData, abstractData );
}

FrozenTrie.prototype = {
    init: function( data, directoryData, nodeCount, letterData, abstractData )
    {
        this.data = new BitString( data );
	this.letterData = letterData;
	this.abstract = abstractData;
        this.directory = new RankDirectory( abstractData, data, 
                nodeCount * 2 + 1, L1, L2 );

        // The position of the first bit of the data in 0th node. In non-root
        // nodes, this would contain 6-bit letters.
        this.letterStart = nodeCount * 2 + 1;
	this.All_found = Object.create(null);
    },

    /**
       Retrieve the FrozenNode of the trie, given its index in level-order.
       This is a private function that you don't have to use.
      */
    getNodeByIndex: function( index )
    {
        let final, letter;

        if (Memoization[index])	// if already constructed a FrozenNode for this index
	    return Memoization[index];

        //hist.push(index);	// profiling debugging

        if (1) {
	    // Retrieve the ASCII character that encodes the letter.
	    // bit[5] is the "final" flag, bits[4:0] is the letter 0..25 => a..z
	    // bit[6] is always clear by design constraint.
	    //
	    let c = this.letterData.charCodeAt(index);

	    final = false;
	    if (c >= 32) {   // Is bit[5] set?
		final = true;
		c = c - 32;  // Clear bit[5] arithmetically
	    }
	    letter = String.fromCharCode( c + 'a'.charCodeAt(0) );
	}
	else {
	    // retrieve the 6-bit letter.
	    final = this.data.get( this.letterStart + index * 6, 1 ) === 1;
	    letter = String.fromCharCode(
		    this.data.get( this.letterStart + index * 6 + 1, 5 ) + 
		    'a'.charCodeAt(0));
	}

        var firstChild = this.directory.select( 0, index+1 ) - index;

//console.log("get NodeByIndex Q", index, letter, final, firstChild);  // debugging

        // Since the nodes are in level order, this node's children must go up
        // until the next node's children start.
	//
        var childOfNextNode = this.directory.select( 0, index + 2 ) - index - 1;

//console.log("get NodeByIndex T", childOfNextNode-firstChild);  // debugging
	
	return Memoization[index] = new FrozenNode( this, index, letter, final, firstChild,
                childOfNextNode - firstChild );
    },  // get NodeByIndex

    /**
      Retrieve the root node.  You can use this node to obtain all of the other
      nodes in the trie.
      */
    getRoot: function()
    {
        return this.getNodeByIndex( 0 );
    },

    movesPossible: function(position) {
	switch(position) {
	case 0 :  return [1, 5, 4];
        case 1 :  return [0, 2, 6, 5, 4];
        case 2 :  return [1, 3, 7, 6, 5];
        case 3 :  return [2, 6, 7];
        case 4 :  return [0, 1, 5, 9, 8];
        case 5 :  return [1, 2, 6, 10, 9, 8, 4, 0];
        case 6 :  return [2, 3, 7, 11, 10, 9, 5, 1];
        case 7 :  return [3, 11, 10, 6, 2];
        case 8 :  return [4, 5, 9, 13, 12];
        case 9 :  return [5, 6, 10, 14, 13, 12, 8, 4];
        case 10 : return [6, 7, 11, 15, 14, 13, 9, 5];
        case 11 : return [7, 15, 14, 10, 6];
        case 12 : return [8, 9, 13];
        case 13 : return [9, 10, 14, 12, 8];
        case 14 : return [10, 11, 15, 13, 9];
        case 15 : return [11, 14, 10];
	default: console.log("Error: movesPossible()");
	}
    },

    getSearchResults: function() {
        return Object.keys(this.All_found).sort();
    },
    detect: function(word) {
        this.All_found[word] = 1;
    },

    // @param base -- This is a FrozenNode
    // @param pos -- a small integer, 0..15, representing a position on a 4x4 puzzle grid
    // @param word -- a string, rep'ing the growing letter sequence that may be a found word
    // @param verboten -- an integer bit vector of grid position verboten to backtrack to
    wordfind: function(base, pos, word, verboten) {
        let letter = Game[pos];
	let child;

	//console.log("wordfind 3", letter);  // debugging

	child = this.getChildByLetter(base, letter);
	if (!child)
	    return;

	// A Q on the grid advances the search up to the U also.
	//
	if ('q' === letter) {
	    letter += 'u';
	    child = this.getChildByLetter(child, 'u');
	}
	if (!child)
	    return;

	if (child.final) {
	    this.detect(word+letter);
	}
	verboten = verboten | (1<<pos);
	for (let next_move of this.movesPossible(pos)) {
	    if (verboten & (1<<next_move))
	        continue;
	    this.wordfind(child, next_move, word+letter, verboten);  // recur
	}
    },

    // @param parent is a FrozenNode
    // @param letter is a string (expect it to be a single character)
    getChildByLetter: function (parent, letter) {
        let child;

	if (parent.cached) {
	    return parent.cachedChildByLetter(letter);
	}

	if (parent.index < 703) {
	    parent.cacheTheChildren();
	    return parent.cachedChildByLetter(letter);
	}

	//console.log("getChildByLetter 3", letter, parent.getChildCount());  // debugging
        for (var idx=0; idx < parent.getChildCount(); ++idx) {
	    child = parent.getChild(idx);
	    //console.log("getChildByLetter 5", child.letter);  // debugging
	    if (child.letter === letter) {
	        return child;
	    }
	    else if (child.letter > letter) {
	        return null;
	    }
	}
	return null;
    },

    /**
      Look-up a word in the trie.  Returns true if and only if the word exists
      in the trie.
      */
    lookup: function( word ) 
    {
        //console.log("lookup", word);  // debugging

        var node = this.getRoot();
        for ( var i = 0; i < word.length; i++ ) {
            var child;
            for ( var j = 0; j < node.getChildCount(); j++ ) {
                child = node.getChild( j );

		//console.log(child.letter);  // debugging

		// If the child node's letter matches what we are seeking,
		// we are done.  Also, since the trie is in sorted order,
		// if this linear search moves beyond the letter we seek,
		// then we know it doesn't exist.   It is therefore a waste of time
		// to examine the remaining children nodes.
		//
                if ( child.letter === word[i] ) {
                    break;
                }
		else if (child.letter > word[i]) {  // short-cut
		    return false;
		}
            }

            if ( j === node.getChildCount() ) {
                return false;
            }
            node = child;
        }
        return node.final;
    }
};// FrozenTrie prototype

function getWords() {
        let wordArr;
	wordArr = ["hat", "it", "is", "a",];
	wordArr = ["hat", "hats", "it", "is", "a", "sax", "saxc",
		"get", "noun", "open", "peach", "rest", "turkey"];
	wordArr = readFile("../boggle/everyday").split('\n');
	//wordArr.length = 500;
	return wordArr;
}

/**
  Encode the trie in the input text box.
  */
function go()
{
    // create a trie
    var trie = new Trie();

    // split the words of the input up.  Sort them for faster trie insertion.
    var words = getWords();

    // [tobin] I suspect this sorting is not just required for
    // "faster trie insertion," but is fundamentally required to make it work.
    // Update: I'm correct: word list must be sorted.
    //
    words.sort();

    // For every word in the array, convert to lowercase and 
    // insert if result is exclusively letters and also non-zero length.
    //
    for ( var i = 0; i < words.length; i++ ) {
        // To save space, our encoding handles only the letters a-z. Ignore
        // words that contain other characters.
        var word = words[i].toLowerCase();
        if ( word.match( /^[a-z]+$/ ) ) {
            trie.insert( word );
        }
    }

    // Encode the trie and represent as base64.
    var trieData = trie.encode();

    // Encode the rank directory
    var directory = RankDirectory.Create( trieData, trie.getNodeCount() * 2 +
            1, L1, L2 );
    var output;
    
    output = '{\n    "nodeCount": ' + trie.getNodeCount() + ",\n";
    
    output += '    "directory": "' + directory.getData() + '",\n';
    
    output += '    "trie": "' + trieData + '"\n';
    output += '}\n';

    if (harvest) console.log(`@ nodeCount ${trie.getNodeCount()}`);

    return output;
}// go()


/**
  Decode the data in the output textarea, and use it to check if a word exists
  in the dictionary.
  */
// @param so  Is a string of a object literal {trie, directory, nodeCount} representing
//            the base64 encoded trie, its directory, and number of non-super nodes.
// @param w   Is a non-empty string of the all-lowercase word to check existence.
function searchTrie(so, w)   
{
    var status = "";
    //try {
        //var json = (so) ? eval(`(${so})`) : eval( '(' + document.getElementById("output").value + ")" );

	//console.log("search Trie 3", w);  // debugging
        //var ftrie = new FrozenTrie( json.trie, json.directory, json.nodeCount);
        var ftrie = new FrozenTrie( encTrie, encDir, nodeCount, encLetter, encAbstract);
        var word = w || document.getElementById("lookup").value;

	//console.log("search Trie 5", word);  // debugging

        if ( ftrie.lookup( word ) ) {
            status = '"' + word + '" is in the dictionary.';
        } else {
            status = '"' + word + '" IS NOT in.';
        }
    //} catch ( e ) {
        //status = "Error. Have you encoded the dictionary yet?";
    //}

    if (w) return status;
    document.getElementById("status").innerHTML = status;
}
function searchGame(so) {
    console.log("searchGame 0", encTrie.length, nodeCount);  // debugging
    //try {
	//let json = JSON.parse(so);  // Used to be: eval(`(${so})`);

	//console.log("searchGame 5", json.nodeCount);  // debugging

        var ftrie = new FrozenTrie( encTrie, encDir, nodeCount, encLetter, encAbstract);
        //var ftrie = new FrozenTrie( json.trie, json.directory, json.nodeCount);

	//console.log("searchGame 7 dir len");  // debugging
	if (0) {
	    let pos = 0;
	    ftrie.wordfind(ftrie.getRoot(), pos, "", 0);
	}
	else {
	for (let pos = 0; pos < 16; ++pos) {
	    ftrie.wordfind(ftrie.getRoot(), pos, "", 0);
	}
	}
	//console.log("searchGame 9");    // debugging
	return ftrie.getSearchResults();
    //} catch (e) { return ["Error. searchGame() Have you encoded the dictionary yet?"]; }
}
return {setGame:    setGame,
	go:         go,
	searchGame: searchGame,
	searchTrie: searchTrie,
        getDS:      getDS,
	getMemo:    getMemo,
	};
}
// END

if (TR_STANDALONE) {
    let start, mid, stop;
    let list = [];
    let puzzle = ["liosysdasertaaga",
    "adqejilluketysbc",
    "ieearcltbtcuivrs",
    "toapyausizeynggy",
    "eyleseeaovtiitqg",
    "toapyausizeynggy",
    "nhwsifbywzehomen",
    "efdtybmwlstvivsm",
    "oeattdmjdcnrofvi",
    "trsentolienaoaam",
    "uhfewsburertdcmn",
    "ejluteifwygtheoe",
    "totaeqaddivyzter",
    "lsloeuweofildstv",
    "asnepufrthwluqds",
    "reynairtetojeton",
    "soigelniiiunstfq",
    "soigelniiiunstfq",
    "edmuetgirxaweesa",
    "nesnimlrnauigaga",
    "qwerasdfzxcvtegb",
    "unxjrkqotzetzdcv",
    "tkjyxqsetzzklmng",
    "awerasdfzxcvtegb",
    "ohgolxsmieseiocl",
    "togsnskiraoasrlr",
    "oikrgsrietihychd",
    ];
    puzzle.length = 7;

    harvest = 0;
    let jstr;
    let solve = mk_solver();
    if (true || harvest) {
        jstr = solve.go();  // retrieve a json string representing the encoded trie
	console.log("length of trie object literal as ASCII", jstr.length);
	if (jstr.length < 800) console.log(solve.getDS());
    }

    if (0) {
      if (jstr.length < 800) {
	  console.log(jstr);   // display the encoded (base64) trie with its directory
      }
    }

if (1) {
    for (let idx = 0; idx < puzzle.length; ++idx) {
        solve.setGame(puzzle[idx]);

	console.log(puzzle[idx]);
	let gg = puzzle[idx].toUpperCase();
	let res = gg.split(/(\w{4})/);
	console.log ( [res[1], res[3], res[5], res[7]].join("\n"));

	start = Date.now();
	let r = solve.searchGame();
	stop = Date.now();

	console.log(r.length, "words found.");
	console.log(r);
	console.log(stop-start, "milliseconds");
	console.log("Memo length", solve.getMemo().length);
    }
}
else {
    while (harvest === 0) {
        console.log("Enter word to lookup:");
        let w = getline().trim();  // calls quit()
	console.log(solve.searchTrie(jstr, w));
    }
    // NOTREACHED
}
}
