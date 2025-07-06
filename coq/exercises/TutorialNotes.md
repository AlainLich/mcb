Hi, my remarks below are based on using version:

   ```
	commit 0b2c571d47196 Date:   Mon May 12 16:32:01 2025 +0200
	with Coq 8-20, Mathcomp 2.4.0
   ```

**Suggestions for improvement on tutorial: Hierarchy Builder by Quentin Vermande**

1. Thanks I found this tutorial **very useful** when trying to put things in practice, whereas the other papers tend to bury the user in (too much) information. However, in case this might help, following are some remarks.  For context *I am a new user* (of HB and mathcomp), and I **did not expect HB to appear** in my exercises involving a Mathcomp tutorial.

1. Missing (This could be a *teaser* early on or an element preparing the conclusion. )


 - An example concerning the special case of having to register a structure with the mathcomp librarie's definitions would help. When (finally) done this means a (long and simple ) series 

	```
	HB.instance Definition _ :=  Equality.copy myStruct myProp.
	HB.instance Definition _ :=  Choice.copy myStruct myProp.
	HB.instance Definition _ :=  Countable.copy myStruct myProp.
	HB.instance Definition _ :=  Finite.copy myStruct myProp.
	```
	Therefore the  `.copy` notation/mechanism could be explained and an example given. (The log output shows these defined by `HB`, as well as `.clone`, `.on`,.. ) Also in the case of mathcomp library, these instances will depend/rely on one another and choosing the right strategy is important.

	

	By the same token, notations like (in 'eqtype.v') `[isSub ...]` could be explained since they may be useful (with their variants) in situation such as:

	``` 
	HB.instance Definition _ := [isSub  for (@tval n T) ].
	```

	This is explained by C.Cohen in <https://github.com/math-comp/math-comp/wiki/How-to-declare-MathComp-instances> (mathcomp wiki), at least for some (important) mathcomp situations; probably with too much detail for a tutorial.

1. Clarification required: 
   - what is the meaning of`#`directives and where do I find a complete list in the documentation?
   For example  what is   `#[short(type="ptType")]`on line 331?

   - Paragraph lines 313-317 seems to recommend to do exactly
the same thing as above (or am  I missing something)
   - Would help to explain that `#[primitive]` and "Primitive Projection" in the manual 
are related 
   - Paragraph 5 (forgetful inheritance). I managed to receive some diagnostic output naming
"forgetful inheritance" for a missing type parameter. So a "do not panic" explanation for the reader might be in  order... mentioning simpler things than questioning the inheritance graph from the start.) 

1. Improvement suggestions
 - Expand discussion of the 'subject' `T` around line 140, or defer to section 4.2 (expanding the
   explanation on the role of `f`). 
   This comes back with the discussion of the `key` around line 166.
   This becomes essential in practice, especially when there are other parameters, possibly abstracted away in a section.

 - Built coercion(s): on line 165, confirmation with a 
   `Print Coercion Paths Semigroup.type Magma.type.` would be welcome. Of course the name returned is long but very explicit.  

 - explain some key elements found in the output of `#[log]`, the part showing the equivalent Coq statements is a source of information when "debugging" (even if very dense...). 
   1. In particular output for structure shows "copy","on", "clone" notations among others... which are useful. Their connection with `HB.instance`is of interest, and may be also the intention concerning their utilisation.

	1. Identifying the added coercions. 
