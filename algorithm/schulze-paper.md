Soc Choice Welf (2011) 36:267–303 DOI 10.1007/s00355-010-0475-4 ~~ORIGINAL PAPER~~ 

# **A new monotonic, clone-independent, reversal symmetric, and condorcet-consistent single-winner election method** 

## **Markus Schulze** 

Received: 16 January 2009 / Accepted: 24 June 2010 / Published online: 11 July 2010 © Springer-Verlag 2010 

**Abstract** In recent years, the Pirate Party of Sweden, the Wikimedia Foundation, the Debian project, the “Software in the Public Interest” project, the Gentoo project, and many other private organizations adopted a new single-winner election method for internal elections and referendums. In this article, we will introduce this method, demonstrate that it satisfies, e.g., resolvability, Condorcet, Pareto, reversal symmetry, monotonicity, and independence of clones and present an O( _C_ ˆ3) algorithm to calculate the winner, where _C_ is the number of alternatives. 

## **1 Introduction** 

One important property of a good single-winner election method is that it minimizes the number of “overruled” voters (according to some heuristic). Because of this reason, the Simpson–Kramer method, that always chooses that alternative whose worst pairwise defeat is the weakest, was very popular over a long time. However, in recent years, the Simpson–Kramer method has been criticized by many social choice theorists. Smith (1973) criticizes that this method does not choose from the top-set of alternatives. Tideman (1987) complains that this method is vulnerable to the strategic nomination of a large number of similar alternatives, so-called _clones_ . And Saari (1994) rejects this method for violating _reversal symmetry_ . A violation of reversal symmetry can lead to strange situations where still the same alternative is chosen when all ballots are reversed, meaning that the same alternative is identified as best one and simultaneously as worst one. 

M. Schulze (B) Berlin, Germany e-mail: Markus.Schulze@Alumni.TU-Berlin.de 

123 

268 

M. Schulze 

**Table 1** Simulations by Wright (2009) 

|Number of alternatives|A (%)|B (%)|C (%)|
|---|---|---|---|
|3|100.0|100.0|100.0|
|4|99.7|98.5|98.2|
|5|99.2|96.0|95.3|
|6|99.1|93.0|92.3|
|7|98.9|90.0|89.1|



A: Probability that the Schulze method conforms with the Simpson–Kramer method B: Probability that the Schulze method conforms with the ranked pairs method C: Probability that the ranked pairs method conforms with the Simpson–Kramer method 

In this article, we will show that only a slight modification (Sect. 4.8) of the Simpson–Kramer method is needed so that the resulting method satisfies the criteria proposed by Smith (Sect. 4.7), Tideman (Sect. 4.6), and Saari (Sect. 4.4). The resulting method will be called _Schulze method_ . Random simulations by Wright (2009) confirmed that, in almost 99% of all instances, the Schulze method conforms with the Simpson–Kramer method (Table 1). In this article, we will prove that, nevertheless, the Schulze method still satisfies all important criteria that are also satisfied by the Simpson–Kramer method, like resolvability (Sect. 4.2), Pareto (Sect. 4.3), monotonicity (Sect. 4.5), and prudence (Sect. 4.9). Because of these reasons, already several private organizations have adopted the Schulze method. The Schulze method is currently used by the Wikimedia Foundation (about 26,000 eligible members), the Pirate Party of Sweden (about 50,000 eligible members), and the Pirate Party of Germany (about 12,000 eligible members). It is also used by the Debian project, the “Software in the Public Interest” (SPI) project, and the Gentoo project, three software projects with about 1,000 resp. 400 resp. 300 eligible members. 

In Sect. 2 of this article, the Schulze method is defined. In Sect. 3, this method is applied to a concrete example. In Sect. 4, this method is analyzed. Short descriptions of this method can also be found in publications by Tideman (2006, pp. 228–232), Stahl and Johnson (2006, pp. 119–129), Camps et al. (2008), McCaffrey (2008), and Börgers (2009, pp. 37–42). This method is also discussed in articles by Yue et al. (2007), Wright (2009), and Rivest and Shen (2010). 

## **2 Definition of the Schulze method** 

## 2.1 Preliminaries 

A _strict partial order_ is a transitive and asymmetric relation “ _x_ ≻ _y_ ”. A _strict weak order_ is a strict partial order with the additional property that also the relation “not _x_ ≻ _y_ ” is transitive. A _profile_ is a finite list _V_ of 0 _< N <_ ∞ strict weak orders each on the same finite set _A_ of 1 _< C <_ ∞ alternatives. “ _a_ ≻ _v b_ ” means “voter _v_ ∈ _V_ strictly prefers alternative _a_ ∈ _A_ to alternative _b_ ∈ _A_ \{ _a_ }”. Input of the proposed 

123 

269 

A new monotonic, clone-independent, reversal symmetric 

method is a profile. Output of the proposed method are (1) a strict partial order _O_ on _A_ and (2) a set ∅ = _S_ ⊆ _A_ of winners. 

Suppose _N_ [ _e, f_ ] is the number of voters who strictly prefer alternative _e_ to alternative _f_ . We presume that the strength of the link _ef_ depends only on _N_ [ _e, f_ ] and _N_ [ _f, e_ ]. Therefore, the strength of the link _ef_ can be denoted ( _N_ [ _e, f_ ] _, N_ [ _f, e_ ]). We presume that a binary relation ≻ _D_ on N0 × N0 is defined such that the link _ef_ is stronger than the link _gh_ if and only if _(N_ [ _e, f_ ] _, N_ [ _f, e_ ] _)_ ≻ _D (N_ [ _g, h_ ] _, N_ [ _h, g_ ] _)_ . _N_ [ _e, f_ ] is the _support_ for the link _ef_ ; _N_ [ _f, e_ ] is its _opposition_ . 

_Example 1_ ( _margin_ ): When the strength of the link _ef_ is measured by _margin_ , then its strength is the difference _N_ [ _e, f_ ] – _N_ [ _f, e_ ] between its support _N_ [ _e, f_ ] and its opposition _N_ [ _f, e_ ] _._ 

_(N_ [ _e, f_ ] _, N_ [ _f, e_ ] _)_ ≻margin _(N_ [ _g, h_ ] _, N_ [ _h, g_ ] _)_ if and 

only if _N_ [ _e, f_ ] − _N_ [ _f, e_ ] _> N_ [ _g, h_ ] − _N_ [ _h, g_ ] _._ 

_Example 2_ ( _ratio_ ): When the strength of the link _ef_ is measured by _ratio_ , then its strength is the ratio _N_ [ _e, f_ ]/ _N_ [ _f, e_ ] between its support _N_ [ _e, f_ ] and its opposition _N_ [ _f, e_ ] _._ 

_(N_ [ _e, f_ ] _, N_ [ _f, e_ ] _)_ ≻ratio _(N_ [ _g, h_ ] _, N_ [ _h, g_ ] _)_ if and only if at least one of the following conditions is satisfied: 

1. _N_ [ _e, f_ ] _> N_ [ _f, e_ ] and _N_ [ _g, h_ ] ≤ _N_ [ _h, g_ ] _._ 

2. _N_ [ _e, f_ ] ≥ _N_ [ _f, e_ ] and _N_ [ _g, h_ ] _< N_ [ _h, g_ ] _._ 

3. _N_ [ _e, f_ ] · _N_ [ _h, g_ ] _> N_ [ _f, e_ ] · _N_ [ _g, h_ ] _._ 

4. _N_ [ _e, f_ ] _> N_ [ _g, h_ ] and _N_ [ _f, e_ ] ≤ _N_ [ _h, g_ ] _._ 

5. _N_ [ _e, f_ ] ≥ _N_ [ _g, h_ ] and _N_ [ _f, e_ ] _< N_ [ _h, g_ ] _._ 

_Example 3_ ( _winning votes_ ): When the strength of the link _ef_ is measured by _winning votes_ , then its strength is measured primarily by its support _N_ [ _e, f_ ] _._ 

_(N_ [ _e, f_ ] _, N_ [ _f, e_ ] _)_ ≻win _(N_ [ _g, h_ ] _, N_ [ _h, g_ ] _)_ if and only if at least one of the following conditions is satisfied: 

1. _N_ [ _e, f_ ] _> N_ [ _f, e_ ] and _N_ [ _g, h_ ] ≤ _N_ [ _h, g_ ] _._ 

2. _N_ [ _e, f_ ] ≥ _N_ [ _f, e_ ]and _N_ [ _g, h_ ] _< N_ [ _h, g_ ] _._ 

3. _N_ [ _e, f_ ] _> N_ [ _f, e_ ] and _N_ [ _g, h_ ] _> N_ [ _h, g_ ] and _N_ [ _e, f_ ] _> N_ [ _g, h_ ] _._ 

4. _N_ [ _e, f_ ] _> N_ [ _f, e_ ] and _N_ [ _g, h_ ] _> N_ [ _h, g_ ] and _N_ [ _e, f_ ] = _N_ [ _g, h_ ] and _N_ [ _f, e_ ] _< N_ [ _h, g_ ]. 

5. _N_ [ _e, f_ ] _< N_ [ _f, e_ ] and _N_ [ _g, h_ ] _< N_ [ _h, g_ ] and _N_ [ _e, f_ ] _> N_ [ _g, h_ ]. 

6. _N_ [ _e, f_ ] _< N_ [ _f, e_ ] and _N_ [ _g, h_ ] _< N_ [ _h, g_ ] and _N_ [ _e, f_ ] = _N_ [ _g, h_ ] and _N_ [ _f, e_ ] _< N_ [ _h, g_ ] _._ 

_Example 4_ ( _losing votes_ ): When the strength of the link _ef_ is measured by _losing votes_ , then its strength is measured primarily by its opposition _N_ [ _f, e_ ] _._ 

_(N_ [ _e, f_ ] _, N_ [ _f, e_ ] _)_ ≻los _(N_ [ _g, h_ ] _, N_ [ _h, g_ ] _)_ if and only if at least one of the following conditions is satisfied: 

1. _N_ [ _e, f_ ] _> N_ [ _f, e_ ] and _N_ [ _g, h_ ] ≤ _N_ [ _h, g_ ]. 

2. _N_ [ _e, f_ ] ≥ _N_ [ _f, e_ ] and _N_ [ _g, h_ ] _< N_ [ _h, g_ ]. 

3. _N_ [ _e, f_ ] _> N_ [ _f, e_ ] and _N_ [ _g, h_ ] _> N_ [ _h, g_ ] and _N_ [ _f, e_ ] _< N_ [ _h, g_ ] _._ 

123 

M. Schulze 

270 

4. _N_ [ _e, f_ ] _> N_ [ _f, e_ ] and _N_ [ _g, h_ ] _> N_ [ _h, g_ ] and _N_ [ _f, e_ ] = _N_ [ _h, g_ ] and _N_ [ _e, f_ ] _> N_ [ _g, h_ ] _._ 

5. _N_ [ _e, f_ ] _< N_ [ _f, e_ ] and _N_ [ _g, h_ ] _< N_ [ _h, g_ ] and _N_ [ _f, e_ ] _< N_ [ _h, g_ ] _._ 

6. _N_ [ _e, f_ ] _< N_ [ _f, e_ ] and _N_ [ _g, h_ ] _< N_ [ _h, g_ ] and _N_ [ _f, e_ ] = _N_ [ _h, g_ ] and _N_ [ _e, f_ ] _> N_ [ _g, h_ ] _._ 

The most intuitive definitions for the strength of a link are its _margin_ and its _ratio_ . However, we only presume that ≻ _D_ is a strict weak order on N0 × N0 with at least the following properties: 







The presumption, that the strength of the link _ef_ depends only on _N_ [ _e, f_ ] and _N_ [ _f, e_ ] _,_ guarantees (1) that the proposed method satisfies anonymity and neutrality, (2) that adding a ballot, on which all alternatives are ranked equally, cannot change the result of the elections, and (3) that the proposed method is a C2 _Condorcet social choice function_ (CSCF) according to Fishburn’s (1977) terminology. 

(2.1.1) says that, when the support of a link increases and its opposition does not increase or when its opposition decreases and its support does not decrease, then the strength of this link increases. So (2.1.1) says that the strength of a link responses to a change of its support or its opposition in the correct manner. (2.1.1) guarantees that the proposed method satisfies resolvability (Sect. 4.2), Pareto (Sect. 4.3), and monotonicity (Sect. 4.5). When each voter _v_ ∈ _V_ casts a linear order ≻ _v_ on _A_ , then all definitions for ≻ _D_ , that satisfy (2.1.1), are identical. 

(2.1.2) says that every pairwise victory is stronger than every pairwise tie and that every pairwise tie is stronger than every pairwise defeat. (2.1.2) guarantees that the proposed method satisfies the Smith criterion (Sect. 4.7). 

_Homogeneity_ means that the result depends only on the proportion of ballots of each type, not on their absolute numbers. (2.1.2) guarantees that the proposed method satisfies homogeneity. 

Suppose ∅ = _M_ ⊂ N0 × N0 is finite and non-empty. Then “max _DM_ ”, the _set of maximum elements_ of _M_ , and “min _DM_ ”, the _set of minimum elements_ of _M_ , are defined as follows: ( _β_ 1 _, β_ 2 _)_ ∈ max _DM_ if and only if (1) ( _β_ 1, _β_ 2 _)_ ∈ _M_ and (2) ( _β_ 1, _β_ 2 _)_ ≻∼ _D_ ( _δ_ 1, _δ_ 2 _)_ ∀ _(δ_ 1 _, δ_ 2 _)_ ∈ _M_ . ( _γ_ 1, _γ_ 2 _)_ ∈ min _DM_ if and only if (1) ( _γ_ 1, _γ_ 2 _)_ ∈ _M_ and (2) ( _γ_ 1, _γ_ 2 _)_ ≺∼ _D_ ( _δ_ 1, _δ_ 2 _)_ ∀ _(δ_ 1, _δ_ 2 _)_ ∈ _M_ . 

123 

A new monotonic, clone-independent, reversal symmetric 

271 

We write “( _β_ 1, _β_ 2 _)_ : = max _DM_ ” and “( _γ_ 1, _γ_ 2 _)_ : = min _DM_ ” for “( _β_ 1, _β_ 2 _)_ is an arbitrarily chosen element of max _DM_ ” and “( _γ_ 1, _γ_ 2 _)_ is an arbitrarily chosen element of min _DM_ ”. 

## 2.2 Basic definitions 

In this section, the Schulze method is defined. A concrete example can be found in Sect. 3. 

Basic idea of the Schulze method is that the _strength_ of the indirect comparison “alternative _a_ vs. alternative _b_ ” is the _strength_ of the _strongest path a_ ≡ _c(_ 1 _), . . . , c(n)_ ≡ _b_ from alternative _a_ ∈ _A_ to alternative _b_ ∈ _A_ \{ _a_ } and that the _strength_ of a path is the _strength(N_ [ _c(i), c(i_ + 1 _)_ ] _, N_ [ _c(i_ + 1 _), c(i)_ ] _)_ of its _weakest link c(i), c(i_ + 1 _)_ . 

A _path_ from alternative _x_ ∈ _A_ to alternative _y_ ∈ _A_ is a sequence of alternatives _c(_ 1 _), . . . , c(n)_ ∈ _A_ with the following properties: 

1. _x_ ≡ _c_ (1). 

2. _y_ ≡ _c_ ( _n_ ). 

3. 2 ≤ _n <_ ∞. 

4. For all _i_ = 1 _, . . . , (n_ − 1 _)_ : _c(i)_ ≡ _c(i_ + 1 _)_ . 

The _strength_ of the path _c(_ 1 _), . . . , c(n)_ is 

min _D_ { _(N_ [ _c(i), c(i_ + 1 _)_ ] _, N_ [ _c(i_ + 1 _), c(i)_ ] _)_ | _i_ = 1 _, . . . , (n_ − 1 _)_ } _._ 

In other words: The strength of a path is the strength of its weakest link. 

_PD_ [ _a, b_ ] := max _D_ {min _D_ { _(N_ [ _c(i), c(i_ + 1 _)_ ] _, N_ [ _c(i_ + 1 _), c(i)_ ] _)_ | _i_ = 1 _, . . . , (n_ − 1 _)_ } | _c(_ 1 _), . . . , c(n)_ is a path from alternative _a_ to alternative _b_ }. 

In other words: _PD_ [ _a, b_ ] ∈ N0 × N0 is the strength of the strongest path from alternative _a_ ∈ _A_ to alternative _b_ ∈ _A_ \{ _a_ } _._ 

The binary relation _O_ on _A_ is defined asfollows : 



As the link _ab_ is already a path from alternative _a_ to alternative _b_ of strength _(N_ [ _a, b_ ] _, N_ [ _b, a_ ] _)_ , we get 



With (2.2.1) and (2.2.3), we get 



123 

M. Schulze 

272 

Furthermore, we get 



Otherwise, if min _D_ { _PD_ [ _a, b_ ] _, PD_ [ _b, c_ ]} was strictly larger than _PD_ [ _a, c_ ] _,_ then this would be a contradiction to the definition of _PD_ [ _a, c_ ] since there would be a path from alternative _a_ to alternative _c_ via alternative _b_ with a strength of more than _PD_ [ _a, c_ ] _._ 

The asymmetry of _O_ follows directly from (2.2.1) and the asymmetry of ≻ _D_ . Furthermore, in Sect. 4.1, we will see that the binary relation _O_ is transitive. This guarantees that there is always at least one winner. 

## 2.3 Implementation 

The strength _PD_ [ _i, j_ ] of the strongest path from alternative _i_ ∈ _A_ to alternative _j_ ∈ _A_ \{ _i_ } can be calculated with the Floyd (1962) algorithm. The runtime to calculate the strengths of all strongest paths is O( _C_ ˆ3), where _C_ is the number of alternatives in _A_ . 

- Input: _N_ [ _i, j_ ] ∈ N0 is the number of voters who strictly prefer alternative _i_ ∈ _A_ to alternative _j_ ∈ _A_ \{ _i_ }. 

- Output: _PD_ [ _i, j_ ] ∈ N0 × N0 is the strength of the strongest path from alternative _i_ ∈ _A_ to alternative _j_ ∈ _A_ \{ _i_ }. 

   - _pred_ [ _i, j_ ] ∈ _A_ \{ _j_ } is the predecessor of alternative _j_ in the strongest path from alternative _i_ ∈ _A_ to alternative _j_ ∈ _A_ \{ _i_ }. 

_O_ is the binary relation as defined in (2.2.1). 

- “ _winner_ [ _i_ ] = _true_ ” if and only if _i_ ∈ _S_ . 

Stage 1 (initialization): 

1 for _i_ := 1 to _C_ 2 begin 3 for _j_ := 1 to _C_ 4 begin 5 if ( _i_ ̸ = _j_ ) then 6 begin 7 _PD_ [ _i, j_ ] := _(N_ [ _i, j_ ] _, N_ [ _j, i_ ] _)_ 8 _pred_ [ _i, j_ ] := _i_ 9 end 10 end 11 end 

123 

A new monotonic, clone-independent, reversal symmetric 

273 

Stage 2 (calculation of the strengths of the strongest paths): 

12 for _i_ := 1 to _C_ 13 begin 14 for _j_ := 1 to _C_ 15 begin 16 if ( _i_ ̸ = _j_ ) then 17 begin 18 for _k_ := 1 to _C_ 19 begin 20 if ( _i_ ̸ = _k_ ) then 21 begin 22 if ( _j_ ̸ = _k_ ) then 23 begin 24 if ( _PD_ [ _j, k_ ] ≺ _D_ min _D_ { _PD_ [ _j, i_ ] _, PD_ [ _i, k_ ]}) then 25 begin 26 _PD_ [ _j, k_ ] := min _D_ { _PD_ [ _j, i_ ] _, PD_ [ _i, k_ ]} 27 _pred_ [ _j, k_ ] := _pred_ [ _i, k_ ] 28 end 29 end 30 end 31 end 32 end 33 end 34 end 

Stage 3 (calculation of the binary relation _O_ and the winners): 

35 for _i_ := 1 to _C_ 36 begin 37 _winner_ [ _i_ ] := _true_ 38 for _j_ := 1 to _C_ 39 begin 40 if ( _i_ = _j_ ) then 41 begin 42 if ( _PD_ [ _j, i_ ] ≻ _D PD_ [ _i, j_ ] _)_ then 43 begin 44 _ji_ ∈ _/ O_ 45 _winner_ [ _i_ ] := _f alse_ 46 end 47 if ( _PD_ [ _j, i_ ]∼<sup>≺</sup> _D PD_ [ _i_ , _j_ ]) then 48 begin 49 _ji_ ∈ _/ O_ 50 end 51 end 52 end 53 end 

123 

M. Schulze 

274 

## **3 Example** 

## _Example 1_ 

8 voters _a_ ≻ _v c_ ≻ _v d_ ≻ _v b_ 2 voters _b_ ≻ _v a_ ≻ _v d_ ≻ _v c_ 4 voters _c_ ≻ _v d_ ≻ _v b_ ≻ _v a_ 4 voters _d_ ≻ _v b_ ≻ _v a_ ≻ _v c_ 3 voters _d_ ≻ _v c_ ≻ _v b_ ≻ _v a_ 

_N_ [ _i, j_ ] ∈ N0 is the number of voters who strictly prefer alternative _i_ ∈ _A_ to alternative _j_ ∈ _A_ \{ _i_ } _._ In example 1, the pairwise matrix _N_ looks as follows: 

||_N_[*,_a_]|_N_[*,_b_]|_N_[*,_c_]|_N_[*,_d_]|
|---|---|---|---|---|
|_N_[_a_,*]|–|8|14|10|
|_N_[_b_,*]|13|–|6|2|
|_N_[_c_,*]|7|15|–|12|
|_N_[_d_,*]|11|19|9|–|



The following digraph illustrates the graph theoretic interpretation of pairwise elections. If _N_ [ _i, j_ ] _> N_ [ _j, i_ ] _,_ then there is a link from vertex _i_ to vertex _j_ of strength ( _N_ [ _i, j_ ] _, N_ [ _j, i_ ]): 



The above digraph can be used to determine the strengths of the strongest paths. In the following, “ _x, (Z_ 1 _, Z_ 2 _), y_ ” means “( _N_ [ _x, y_ ] _, N_ [ _y, x_ ] _)_ = _(Z_ 1 _, Z_ 2 _)_ ”. 

- _a_ → _b_ : There are 2 paths from alternative _a_ to alternative _b_ . 

Path 1: _a_ , (14,7), _c_ , (15,6), _b_ 

with a strength of min _D_ { (14,7), (15,6) } ≈ _D_ (14,7). 

Path 2: _a_ , (14,7), _c_ , (12,9), _d_ , (19,2), _b_ 

with a strength of min _D_ { (14,7), (12,9), (19,2) } ≈ _D_ (12,9). 

So the strength of the strongest path from alternative _a_ to alternative _b_ is max _D_ { (14,7), (12,9) } ≈ _D_ (14,7). 

123 

275 

A new monotonic, clone-independent, reversal symmetric 

- _a_ → _c_ : There is only one path from alternative _a_ to alternative _c_ . Path 1: _a_ , (14,7), _c_ with a strength of (14,7). 

- _a_ → _d_ : There is only one path from alternative _a_ to alternative _d_ . Path 1: _a_ , (14,7), _c_ , (12,9), _d_ 

      - with a strength of min _D_ { (14,7), (12,9) } ≈ _D_ (12,9). 

- _b_ → _a_ : There is only one path from alternative _b_ to alternative _a_ . Path 1: _b_ , (13,8), _a_ with a strength of (13,8). 

- _b_ → _c_ : There is only one path from alternative _b_ to alternative _c_ . Path 1: _b_ , (13,8), _a_ , (14,7), _c_ 

      - with a strength of min _D_ { (13,8), (14,7) } ≈ _D_ (13,8). 

- _b_ → _d_ : There is only one path from alternative _b_ to alternative _d_ . Path 1: _b_ , (13,8), _a_ , (14,7), _c_ , (12,9), _d_ 

      - with a strength of min _D_ { (13,8), (14,7), (12,9) } ≈ _D_ (12,9). 

- _c_ → _a_ : There are 3 paths from alternative _c_ to alternative _a_ . Path 1: _c_ , (15,6), _b_ , (13,8), _a_ 

   - with a strength of min _D_ { (15,6), (13,8) } ≈ _D_ (13,8). 

   - Path 2: _c_ , (12,9), _d_ , (11,10), _a_ 

   - with a strength of min _D_ { (12,9), (11,10) } ≈ _D_ (11,10). 

   - Path 3: _c_ , (12,9), _d_ , (19,2), _b_ , (13,8), _a_ with a strength of min _D_ { (12,9), (19,2), (13,8) } ≈ _D_ (12,9). 

   - So the strength of the strongest path from alternative _c_ to alternative _a_ is max _D_ { (13,8), (11,10), (12,9) } ≈ _D_ (13,8). 

- _c_ → _b_ : There are 2 paths from alternative _c_ to alternative _b_ . Path 1: _c_ , (15,6), _b_ with a strength of (15,6). Path 2: _c_ , (12,9), _d_ , (19,2), _b_ 

   - with a strength of min _D_ { (12,9), (19,2) } ≈ _D_ (12,9). 

   - So the strength of the strongest path from alternative _c_ to alternative _b_ is max _D_ { (15,6), (12,9) } ≈ _D_ (15,6). 

- _c_ → _d_ : There is only one path from alternative _c_ to alternative _d_ . Path 1: _c_ , (12,9), _d_ with a strength of (12,9). 

- _d_ → _a_ : There are 2 paths from alternative _d_ to alternative _a_ . Path 1: _d_ , (11,10), _a_ with a strength of (11,10). Path 2: _d_ , (19,2), _b_ , (13,8), _a_ 

   - with a strength of min _D_ { (19,2), (13,8) } ≈ _D_ (13,8). 

   - So the strength of the strongest path from alternative _d_ to alternative _a_ is max _D_ { (11,10), (13,8) } ≈ _D_ (13,8). 

- _d_ → _b_ : There are 2 paths from alternative _d_ to alternative _b_ . Path 1: _d_ , (11,10), _a_ , (14,7), _c_ , (15,6), _b_ 

   - with a strength of min _D_ { (11,10), (14,7), (15,6) } ≈ _D_ (11,10). 

   - Path 2: _d_ , (19,2), _b_ with a strength of (19,2). 

123 

276 

M. Schulze 

   - So the strength of the strongest path from alternative _d_ to alternative _b_ is max _D_ { (11,10), (19,2) } ≈ _D_ (19,2). 

- _d_ → _c_ : There are 2 paths from alternative _d_ to alternative _c_ . Path 1: _d_ , (11,10), _a_ , (14,7), _c_ 

   - with a strength of min _D_ { (11,10), (14,7) } ≈ _D_ (11,10). 

   - Path 2: _d_ , (19,2), _b_ , (13,8), _a_ , (14,7), _c_ 

   - with a strength of min _D_ { (19,2), (13,8), (14,7) } ≈ _D_ (13,8). 

   - So the strength of the strongest path from alternative _d_ to alternative _c_ is max _D_ { (11,10), (13,8) } ≈ _D_ (13,8). 

The following table lists the strongest paths. The critical links of the strongest paths are underlined: 

||... to_a_|... to_b_|... to_c_|... to_d_|
|---|---|---|---|---|
|from_a_...|–|_a_,(14,7)<br>,_c_,|_a_,(14,7)<br>,_c_|_a_, (14,7),_c_,|
|||(15,6),_b_||(12,9)<br>,_d_|
|from_b_...|_b_,(13,8)<br>,_a_|–|_b_, (13,8)<br>, _a_,|_b_, (13,8),_a_,|
||||(14,7),_c_|(14,7),_c_,<br>(12,9)<br>,_d_|
|from_c_...|_c_, (15,6),_b_,|_c_,(15,6)<br>,_b_|–|_c_,(12,9)<br>,_d_|
||(13,8)<br>,_a_||||
|from_d_...|_d_, (19,2),_b_,|_d_,(19,2)<br>,_b_|_d_, (19,2),_b_,|–|
||(13,8)<br>,_a_||(13,8)<br>,_a_,||
||||(14,7),_c_||



The strengths of the strongest paths are: 

||_PD_[*,_a_]|_PD_[*,_b_]|_PD_[*,_c_]|_PD_[*,_d_]|
|---|---|---|---|---|
|_PD_[_a,_∗]|–|(14,7)|(14,7)|(12,9)|
|_PD_[_b_,*]|(13,8)|–|(13,8)|(12,9)|
|_PD_[_c_,*]|(13,8)|(15,6)|–|(12,9)|
|_PD_[_d_,*]|(13,8)|(19,2)|(13,8)|–|



_xy_ ∈ _O_ if and only if _PD_ [ _x, y_ ] ≻ _D PD_ [ _y, x_ ] _._ So in example 1, we get _O_ = { _ab, ac, cb, da, db, dc_ } _._ 

_x_ ∈ _S_ if and only if _yx_ ∈ _/ O_ for all _y_ ∈ _A_ \{ _x_ }. So in example 1, we get _S_ = { _d_ }. 

## **4 Analysis of the Schulze method** 

## 4.1 Transitivity 

In this section, we will prove that the binary relation _O_ , as defined in (2.2.1), is _transitive_ . This means: If _ab_ ∈ _O_ and _bc_ ∈ _O_ , then _ac_ ∈ _O_ . This guarantees that the set _S_ of winners, as defined in (2.2.2), is non-empty. When we interpret the Schulze method as a method to find a set _S_ of winners, rather than a method to generate a binary relation _O_ , then the proof of the transitivity of _O_ is an essential part of the proof that the Schulze method is well defined. 

123 

A new monotonic, clone-independent, reversal symmetric 

277 

**Definition** An election method satisfies _transitivity_ if the following holds for all _a, b, c_ ∈ _A_ : 

Suppose: 



Then: 



**Claim** The binary relation _O_ , as defined in (2.2.1), is transitive. _Proof_ With (4.1.1), we get 



With (4.1.2), we get 



With (2.2.5), we get 



Case 1: Suppose 



Combining (4.1.5) and (4.1.9a) gives 



Combining (4.1.8) and (4.1.10a) gives 



Combining (4.1.6) and (4.1.9a) gives 



Combining (4.1.11a), (4.1.5), and (4.1.12a) gives 



123 

M. Schulze 

278 

With (4.1.13a), we get (4.1.3). 

Case 2: Suppose 



Combining (4.1.4) and (4.1.9b) gives 



Combining (4.1.7) and (4.1.10b) gives 



Combining (4.1.6) and (4.1.9b) gives 



Combining (4.1.11b), (4.1.4), and (4.1.12b) gives 



With (4.1.13b), we get (4.1.3). ⊓⊔ 

The following corollary says that the set _S_ of winners, as defined in (2.2.2), is non-empty: 

**Corollary** _For the Schulze method, as defined in Sect. 2.2, we get_ 



_Proof of the corollary_ As _b_ ∈ _/ S_ , there must be a _c(_ 1 _)_ ∈ _A_ with _c(_ 1 _), b_ ∈ _O_ . 

If _c(_ 1 _)_ ∈ _S_ , then the corollary is proven. If _c(_ 1 _)_ ∈ _/ S_ , then there must be a _c(_ 2 _)_ ∈ _A_ with _c(_ 2 _), c(_ 1 _)_ ∈ _O_ . With the transitivity and the asymmetry of _O_ , we get _c(_ 2 _), b_ ∈ _O_ and _c(_ 2 _)_ ∈{ _/ b, c(_ 1 _)_ } _._ 

We now proceed as follows: If _c(i)_ ∈ _S_ , then the corollary is proven. If _c(i)_ ∈ _/ S_ , then there must be a _c(i_ + 1 _)_ ∈ _A_ with _c(i_ + 1 _), c(i)_ ∈ _O_ . With the transitivity and the asymmetry of _O_ , we get _c(i_ + 1 _), b_ ∈ _O_ and _c(i_ + 1 _)_ ∈{ _/ b, c(_ 1 _), ..., c(i)_ } _._ 

We proceed until _c(i)_ ∈ _S_ for some _i_ ∈ N. Such an _i_ ∈ N exists because _A_ is finite. 

⊓⊔ 

## 4.2 Resolvability 

_Resolvability_ basically says that usually there is a unique winner _S_ = { _a_ }. There are two different versions of the resolvability criterion. We will prove that the Schulze method, as defined in Sect. 2.2, satisfies both. 

123 

A new monotonic, clone-independent, reversal symmetric 

279 

## _4.2.1 Formulation #1_ 

**Definition** An election method satisfies the first version of the _resolvability criterion_ if (for every given number of alternatives) the proportion of profiles without a unique winner tends to zero as the number of voters in the profile tends to infinity. 

**Claim** If ≻ _D_ satisfies (2.1.1), then the Schulze method, as defined in Sect. 2.2, satisfies the first version of the resolvability criterion. 

## _Proof_ (overview) 

Suppose ( _x_ 1 _, x_ 2 _), (y_ 1 _, y_ 2 _)_ ∈ N0 × N0. Then, according to (2.1.1), there is a _v_ 1 ∈ N0 such that for all _w_ 1 ∈ N0: 

1. _w_ 1 _< v_ 1 �⇒ _(x_ 1 _, x_ 2 _)_ ≻ _D (w_ 1 _, y_ 2 _)_ . 

2. _w_ 1 _> v_ 1 �⇒ _(x_ 1 _, x_ 2 _)_ ≺ _D (w_ 1 _, y_ 2 _)_ . 

When the number of voters tends to infinity (i.e., when _x_ 1 _, x_ 2 _, y_ 1, and _y_ 2 become large), then the proportion of profiles, where the condition “ _y_ 1 = _v_ 1” happens to be satisfied, tends to zero. Therefore, when the number of voters tends to infinity, then the proportion of profiles, where two links _ef_ and _gh_ happen to have equivalent strengths _(N_ [ _e, f_ ] _, N_ [ _f, e_ ] _)_ ≈ _D (N_ [ _g, h_ ] _, N_ [ _h, g_ ] _),_ tends to zero. 

Therefore, we will prove that, unless there are links _ef_ and _gh_ of equivalent strengths, there is always a unique winner. We will prove this by showing that, when we simultaneously presume (a) that there is more than one winner and (b) that there are no links _ef_ and _gh_ of equivalent strengths, then we necessarily get to a contradiction. 

## _Proof_ (details) 

Suppose that there is more than one winner. Suppose alternative _a_ ∈ _A_ and alternative _b_ ∈ _A_ are winners. Then 



Suppose there are no links _ef_ and _gh_ of equivalent strengths ( _N_ [ _e, f_ ] _, N_ [ _f, e_ ] _)_ ≈ _D (N_ [ _g, h_ ] _, N_ [ _h, g_ ] _)_ . Then _PD_ [ _a, b_ ] ≈ _D PD_ [ _b, a_ ] means that the weakest link in the strongest path from alternative _a_ to alternative _b_ and the weakest link in the strongest path from alternative _b_ to alternative _a_ must be the same link, say _cd_ . Therefore, the strongest paths have the following structure: 

123 

M. Schulze 

280 



As _cd_ is the weakest link in the strongest path from alternative _a_ to alternative _b_ , we get 



As _cd_ is the weakest link in the strongest path from alternative _b_ to alternative _a_ , we get 



With (4.2.1.7), (4.2.1.3), and (4.2.1.4), we get 



But (4.2.1.8) contradicts (4.2.1.1). Similarly, with (4.2.1.5), (4.2.1.3), and (4.2.1.6), we get 



But (4.2.1.9) contradicts (4.2.1.2). ⊓⊔ 

## _4.2.2 Formulation #2_ 

The second version of the _resolvability criterion_ says that, when there is more than one winner, then, for every alternative _a_ ∈ _S_ , it is sufficient to add a single ballot _w_ so that alternative _a_ becomes the unique winner. 

**Definition** An election method satisfies the second version of the _resolvability criterion_ if the following holds: 

> ∀ _a_ ∈ _S_<sup>old</sup> : It is possible to construct a strict weak order _w_ such that _S_<sup>new</sup> = { _a_ }for _V_<sup>new</sup> := _V_<sup>old</sup> + { _w_ } _._ 

123 

A new monotonic, clone-independent, reversal symmetric 

281 

**Claim** If ≻ _D_ satisfies (2.1.1), then the Schulze method, as defined in Sect. 2.2, satisfies the second version of the resolvability criterion. 

_Proof_ Suppose _a_ ∈ _S_<sup>old</sup> . Then we get 



Suppose the strict weak order _w_ is chosen as follows: 



With (4.2.2.2), we get 



We will prove the following three claims: 

Claim #1: It is not possible that (4.2.2.2) requires _e_ ≻ _w f_ and that simultaneously (4.2.2.3) requires _f_ ≻ _w e_ . 

Claim #2: ∀ _g_ ∈ _A_ \ { _a_ } : _PD_<sup>new</sup> [ _a, g_ ] ≻ _D PD_<sup>old[</sup><sup>_a, g_]</sup><sup>_._</sup> Claim #3: ∀ _g_ ∈ _A_ \ { _a_ } : _PD_<sup>new</sup> [ _g, a_ ] ≺ _D PD_<sup>old[</sup><sup>_a, g_]</sup><sup>_._</sup> 

With claim #2 and claim #3, we get 



so that _ag_ ∈ _O_<sup>new</sup> for all _g_ ∈ _A_ \{ _a_ } so that _S_<sup>new</sup> = { _a_ }. 

_Proof of claim #1:_ Suppose _e, f_ ∈ _A_ \{ _a_ } _._ With (2.2.3), we get 



With (2.2.5), we get 



With (4.2.2.1), we get 



Suppose (4.2.2.2) requires _e_ ≻ _w f._ Then _e_ = _pred_<sup>old</sup> [ _a, f_ ] _._ Therefore, the link _ef_ was in the strongest path from alternative _a_ to alternative _f_ . Thus, we get 



123 

M. Schulze 

282 

Suppose (4.2.2.3) requires _f_ ≻ _w e_ . Then 



With (4.2.2.5), (4.2.2.8), (4.2.2.7), and (4.2.2.9), we get 



But (4.2.2.9) and (4.2.2.10) together contradict (4.2.2.6). 

_Proof of claim #2:_ With (2.1.1) and (4.2.2.2), we get: The strength of each link of the strongest paths from alternative _a_ to each other alternative _g_ ∈ _A_ \{ _a_ } is increased. Therefore, 



_Proof of claim #3:_ Suppose _g_ ∈ _A_ \{ _a_ } _._ Suppose 



With (4.2.2.1) and (4.2.2.12), we get 



and, therefore, ∅ = T _(g)_ ⊊ _A_ . Furthermore, we get 

∀ _i_ ∈ _/_ T _(g)_ ∀ _j_ ∈ T _(g)_ : _N_<sup>old</sup> [ _i, j_ ] _, N_<sup>old</sup> [ _j, i_ ] ≺∼ _D PD_<sup>old[</sup><sup>_a, g_]</sup><sup>_._(4.2.2.14)</sup> � � 

Otherwise, there was a path from alternative _i_ to alternative _a_ via alternative _j_ with a strength of more than _PD_<sup>old[</sup><sup>_a, g_]</sup><sup>_._But (as</sup><sup>_i_∈</sup><sup>_/_T</sup><sup>_(g)_) this would contradict the definition</sup> of T _(g)_ . 

With (4.2.2.3), (4.2.2.4), and (4.2.2.12), we get 



With (2.1.1) and (4.2.2.15), we get 



With (4.2.2.14) and (4.2.2.16), we get 



123 

A new monotonic, clone-independent, reversal symmetric 

283 

With (4.2.2.13) and (4.2.2.17), we get 



## 4.3 Pareto 

The _Pareto criterion_ says that the election method must respect unanimous opinions. There are two different versions of the Pareto criterion. The first version addresses situations with “ _a_ ≻ _v b_ for all _v_ ∈ _V_ ”, while the second version addresses situations with “ _a_ ∼<sup>≻</sup> _v b_ for all _v_ ∈ _V_ ” (for some pair of alternatives _a, b_ ∈ _A_ ). The first version says that, when every voter strictly prefers alternative _a_ to alternative _b_ (i.e., _a_ ≻ _v b_ for all _v_ ∈ _V_ ), then alternative _a_ must perform better than alternative _b_ . The second version says that, when no voter strictly prefers alternative _b_ to alternative _a_ (i.e., _a_ ∼<sup>≻</sup> _v b_ for all _v_ ∈ _V_ ), then alternative _b_ must not perform better than alternative _a_ . We will prove that the Schulze method, as defined in Sect. 2.2, satisfies both versions of the Pareto criterion. 

## _4.3.1 Formulation #1_ 

**Definition** An election method satisfies the first version of the _Pareto criterion_ if the following holds: 

Suppose: 



Then: 



**Claim** If ≻ _D_ satisfies (2.1.1), then the Schulze method, as defined in Sect. 2.2, satisfies 

_Proof_ With (2.1.1) and (4.3.1.1), we get 



With (2.2.4), we get: _ab_ ∈ _O_ , unless the link _ab_ is in a directed cycle that consists of links of which each is at least as strong as the link _ab_ . 

However, as we presumed that the individual ballots ≻ _v_ are transitive, it is not possible that there is a directed cycle of unanimous opinions. Therefore, it is not possible that the link _ab_ is in a directed cycle that consists of links of which each is at least as 

123 

M. Schulze 

284 

strong as the link _ab_ . Therefore, with (2.2.4), (4.3.1.4), and (4.3.1.5), we get (4.3.1.2). With (4.3.1.2), we get (4.3.1.3). ⊓⊔ 

## _4.3.2 Formulation #2_ 

**Definition** An election method satisfies the second version of the _Pareto criterion_ if the following holds: 

Suppose: 



Then: 



**Claim** If ≻ _D_ satisfies (2.1.1), then the Schulze method, as defined in Sect. 2.2, satisfies the second version of the Pareto criterion. 

_Proof_ With (4.3.2.1), we get 



With (4.3.2.1), we get 



With (2.1.1), (4.3.2.6), and (4.3.2.7), we get 



With (2.1.1), (4.3.2.6), and (4.3.2.7), we get 



Suppose _c(_ 1 _), . . . , c(n)_ ∈ _A_ is the strongest path from alternative _b_ to alternative _a_ . With (4.3.2.8) and (4.3.2.9), we get: _a, c(_ 2 _), . . ., c(n_ − 1 _), b_ is a path from alternative _a_ to alternative _b_ with at least the same strength. Therefore, 



With (4.3.2.10), we get (4.3.2.2). 

Suppose _c(_ 1 _), . . ., c(n)_ ∈ _A_ is the strongest path from alternative _b_ to alternative _f_ ∈ _A_ \{ _a, b_ } _._ With (4.3.2.8), we get: _a, c(m_ + 1 _), . . . , c(n),_ where _c(m)_ is the last 

123 

285 

A new monotonic, clone-independent, reversal symmetric 

occurrence of an alternative of the set { _a, b_ } _,_ is a path from alternative _a_ to alternative _f_ with at least the same strength. Therefore, 



Suppose _c(_ 1 _), . . . , c(n)_ ∈ _A_ is the strongest path from alternative _f_ ∈ _A_ \{ _a, b_ } to alternative _a_ . With (4.3.2.9), we get: _c(_ 1 _), . . . , c(m_ − 1 _), b,_ where _c(m)_ is the first occurrence of an alternative of the set { _a, b_ } _,_ is a path from alternative _f_ to alternative _b_ with at least the same strength. Therefore, 



Part 1: Suppose _f_ ∈ _A_ \{ _a, b_ }. Suppose 



With (4.3.2.13a), we get 



With (4.3.2.11), (4.3.2.14a), and (4.3.2.12), we get 

_PD_ [ _a, f_ ] ∼<sup>≻</sup> _D PD_ [ _b, f_ ] ≻ _D PD_ [ _f, b_ ] ∼<sup>≻</sup> _D PD_ [ _f, a_ ] _._ (4.3.2.15a) 

With (4.3.2.15a), we get (4.3.2.3). Part 2: Suppose _f_ ∈ _A_ \{ _a, b_ } _._ Suppose 



With (4.3.2.13b), we get 



With (4.3.2.12), (4.3.2.14b), and (4.3.2.11), we get 



With (4.3.2.15b), we get (4.3.2.4). Part 3: Suppose 



With (4.3.2.13c), we get 



123 

286 

M. Schulze 

With (4.3.2.4) and (4.3.2.14c), we get 



With (4.3.2.2) and (4.3.2.15c), we get 



With (4.3.2.16c), we get (4.3.2.5). ⊓⊔ 

## 4.4 Reversal symmetry 

_Reversal symmetry_ as a criterion for single-winner election methods has been proposed by Saari (1994). This criterion says that, when ≻ _v_ is reversed for all _v_ ∈ _V_ , then also the result of the elections must be reversed; see (4.4.2). When alternative _a_ ∈ _A_ was the unique winner in the original situation (i.e., _S_<sup>old</sup> = { _a_ }), then alternative _a_ ∈ _A_ should not be a winner in the reversed situation (i.e., _a_ ∈ _/ S_<sup>new</sup> _)_ ; see (4.4.3). It should not be possible that the same alternatives are elected in the original situation and in the reversed situation, unless all alternatives are tied; see (4.4.4). 

Basic idea of this criterion is that, when there is a vote on the best alternatives and then there is a vote on the worst alternatives and when in both cases the same alternatives are chosen, then this questions the logic of the underlying heuristic of the used election method. 

**Definition** An election method satisfies _reversal symmetry_ if the following holds: Suppose: 



Then: 



**Claim** The Schulze method, as defined in Sect. 2.2, satisfies reversal symmetry. 

_Proof_ With (4.4.1), we get 



123 

A new monotonic, clone-independent, reversal symmetric 

287 

With (4.4.5), we get 



With (4.4.6), we get: When _c(_ 1 _), . . . , c(n)_ ∈ _A_ was a path from alternative _g_ ∈ _A_ to alternative _h_ ∈ _A_ \{ _g_ } _,_ then _c(n), . . . , c(_ 1 _)_ is a path from alternative _h_ to alternative _g_ with the same strength. Therefore, 



With (4.4.7), we get (4.4.2). 

- Part 1: Suppose ∃ _i_ ∈ _A_ : _i_ ∈ _S_<sup>old</sup> and _i_ ∈ _/ S_<sup>new</sup> . With _i_ ∈ _/ S_<sup>new</sup> and (4.1.14), we get that there is a _j_ ∈ _S_<sup>new</sup> with _ji_ ∈ _O_<sup>new</sup> . With (4.4.2), we get _i j_ ∈ _O_<sup>old</sup> and, therefore, _j_ ∈ _/ S_<sup>old</sup> . With _j_ ∈ _/ S_<sup>old</sup> and _j_ ∈ _S_<sup>new</sup> , we get the “�⇒” direction of (4.4.3). The proof for the “⇐�” direction of (4.4.3) is analogous. 

- Part 2: Suppose _S_<sup>old</sup> = _A_ . Then we get _O_<sup>old</sup> = ∅ _._ Otherwise, if there was an _i j_ ∈ _O_<sup>old</sup> , we would immediately get _j_ ∈ _/ S_<sup>old</sup> and, therefore, _S_<sup>old</sup> = _A_ . With _O_<sup>old</sup> = ∅ and (4.4.2), we get _O_<sup>new</sup> = ∅ and, therefore, _S_<sup>new</sup> = _A_ . With _S_<sup>old</sup> = _A_ and _S_<sup>new</sup> = _A_ , we get _S_<sup>old</sup> = _S_<sup>new</sup> . 

- Part 3: Suppose _S_<sup>old</sup> = _A_ . Then there is a _j_ ∈ _/ S_<sup>old</sup> . With (4.1.14), we get that there is an _i_ ∈ _S_<sup>old</sup> with _i j_ ∈ _O_<sup>old</sup> . With (4.4.2), we get _ji_ ∈ _O_<sup>new</sup> and, therefore, _i_ ∈ _/ S_<sup>new</sup> . With _i_ ∈ _S_<sup>old</sup> and _i_ ∈ _/ S_<sup>new</sup> , we get _S_<sup>old</sup> = _S_<sup>new</sup> . With part 2 and part 3, we get (4.4.4). ⊓⊔ 

## 4.5 Monotonicity 

_Monotonicity_ says that, when some voters rank alternative _a_ ∈ _A_ higher (see (4.5.1) and (4.5.2)) without changing the order in which they rank the other alternatives relatively to each other (see (4.5.3)), then this must not hurt alternative _a_ (see (4.5.6)). Monotonicity is also known as _mono-raise_ and _non-negative responsiveness_ . 

**Definition** An election method satisfies _monotonicity_ if the following holds: 

Suppose _a_ ∈ _A_ . Suppose the ballots are modified in such a manner that the following three statements are satisfied: 



123 

M. Schulze 

288 

Then: 

|∀_b_∈_A_\ {_a_} :_ab_∈_O_<sup>old </sup>⇒_ab_∈_O_<sup>new</sup>_._|(4.5.4)|
|---|---|
|∀_b_∈_A_\ {_a_} :_ba /_∈_O_<sup>old </sup>⇒_ba /_∈_O_<sup>new</sup>_._|(4.5.5)|
|_a_ ∈_S_<sup>old </sup>⇒_a_ ∈_S_<sup>new </sup>⊆_S_<sup>old</sup>_._|(4.5.6)|



**Claim** If ≻ _D_ satisfies (2.1.1), then the Schulze method, as defined in Sect. 2.2, satisfies monotonicity. 

_Proof_ Part 1: With (4.5.1), we get 



With (4.5.2), we get 



With (4.5.3), we get 



With (2.1.1), (4.5.7), and (4.5.8), we get 



With (2.1.1), (4.5.7), and (4.5.8), we get 



With (4.5.9), we get 



Suppose _c(_ 1 _), . . . , c(n)_ ∈ _A_ was the strongest path from alternative _a_ to alternative _b_ ∈ _A_ \{ _a_ } _._ Then with (4.5.10) and (4.5.12), we get: _c_ (1),…, _c_ ( _n_ ) is a path from alternative _a_ to alternative _b_ with at least the same strength. Therefore, 



123 

A new monotonic, clone-independent, reversal symmetric 

289 

Suppose _c(_ 1 _), . . . , c(n)_ ∈ _A_ is the strongest path from alternative _b_ ∈ _A_ \{ _a_ } to alternative _a_ . Then with (4.5.11) and (4.5.12), we get: _c_ (1),…, _c_ ( _n_ ) was a path from alternative _b_ to alternative _a_ with at least the same strength. Therefore, 



With (4.5.13) and (4.5.14), we get (4.5.4) and (4.5.5). 

Part 2: It remains to prove (4.5.6). Suppose _a_ ∈ _S_<sup>old</sup> . Then “ _a_ ∈ _S_<sup>new</sup> ” follows directly from (4.5.5). To prove “ _S_<sup>new</sup> ⊆ _S_<sup>old</sup> ”, we have to prove: _h_ ∈ _/ S_<sup>old</sup> �⇒ _h_ ∈ _/ S_<sup>new</sup> . As _a_ ∈ _S_<sup>old</sup> , we get 



Suppose _h_ ∈ _/ S_<sup>old</sup> . Then there must have been an alternative _g_ ∈ _A_ \{ _h_ } with 



With (4.5.10–4.5.12) and (4.5.16), we get: _PD_<sup>new</sup> [ _g, h_ ] ≻ _D PD_<sup>new</sup> [ _h, g_ ] _,_ unless at least one of the following two cases occurred. 

Case 1: _xa_ was a weakest link in the strongest path from alternative _g_ to alternative _h_ . 

Case 2: _ay_ was the weakest link in the strongest path from alternative _h_ to alternative _g_ . 

With (4.5.15), we get: _PD_<sup>old[</sup><sup>_a, h_]≻∼</sup> _D_<sup>_P_</sup> _D_<sup>old[</sup><sup>_h, a_]</sup><sup>_._For</sup><sup>_P_</sup> _D_<sup>old[</sup><sup>_a, h_]≻</sup><sup>_DP_</sup> _D_<sup>old</sup> [ _h, a_ ] _,_ we would, with (4.5.4), immediately get _PD_<sup>new</sup> [ _a, h_ ] ≻ _D PD_<sup>new</sup> [ _h, a_ ] _,_ so that alternative _h_ is still not a winner. Therefore, without loss of generality, we can presume _g_ ∈ _A_ \{ _a, h_ } and 



With (4.5.15), we get 



With (2.2.5), we get 



123 

M. Schulze 

290 

Case 1: Suppose _xa_ was a weakest link in the strongest path from alternative _g_ to alternative _h_ . Then 





Now (4.5.18), (4.5.21a), and (4.5.16) give 



while (4.5.17), (4.5.22a), and (4.5.16) give 



But (4.5.23a) and (4.5.24a) together contradict (4.5.20). 

Case 2: Suppose _ay_ was the weakest link in the strongest path from alternative _h_ to alternative _g_ . Then 





Now (4.5.22b), (4.5.21b), and (4.5.18) give 



while (4.5.16), (4.5.21b), and (4.5.18) give 



But (4.5.23b) and (4.5.24b) together contradict (4.5.19). 

We have proven that neither case 1 nor case 2 is possible. Therefore, 



With (4.5.25), we get: _h_ ∈ _/ S_<sup>new</sup> . ⊓⊔ 

123 

A new monotonic, clone-independent, reversal symmetric 

291 

## 4.6 Independence of clones 

_Independence of clones_ as a criterion for single-winner election methods has been proposed by Tideman (1987). This criterion says that running a large number of similar alternatives, so-called _clones_ , must not have any impact on the result of the elections. 

The precise definition for a _set of clones_ stipulates that every voters ranks all the alternatives of this set in a consecutive manner; see (4.6.1) and (4.6.2). Replacing an alternative _d_ ∈ _A_<sup>old</sup> by a set of clones _K_ should not change the winner; see (4.6.7) and (4.6.8). 

This criterion is very desirable especially for referendums because, while it might be difficult to find several candidates who are simultaneously sufficiently popular to campaign with them and sufficiently similar to misuse them for this strategy, it is usually very simple to formulate a large number of almost identical proposals. For example: In 1969, when the Canadian city that is now known as _Thunder Bay_ was amalgamating, there was some controversy over what the name should be. In opinion polls, a majority of the voters preferred the name _The Lakehead_ to the name _Thunder Bay_ . But when the polls opened, there were three names on the referendum ballot: _Thunder Bay_ , _Lakehead_ , and _The Lakehead_ . As the ballots were counted using _plurality voting_ , it was not a surprise when _Thunder Bay_ won. The votes were as follows: _Thunder Bay_ 15870, _Lakehead_ 15302, _The Lakehead_ 8377. 

**Definition** An election method is _independent of clones_ if the following holds: Suppose _d_ ∈ _A_<sup>old</sup> . Suppose _A_<sup>new</sup> := _(A_<sup>old</sup> ∪ _K )_ \{ _d_ } _._ 

Suppose alternative _d_ is replaced by the set of alternatives _K_ in such a manner that the following three statements are satisfied: 



Then the following statements are satisfied: 



**Claim** The Schulze method, as defined in Sect. 2.2, is independent of clones. 

_Proof_ With (4.6.1), we get 



123 

M. Schulze 

292 

With (4.6.2), we get 



With (4.6.3), we get 



With (4.6.9) and (4.6.10), we get 



With (4.6.9) and (4.6.10), we get 



With (4.6.11), we get 



Suppose _c(_ 1 _), . . . , c(n)_ ∈ _A_<sup>old</sup> was the strongest path from alternative _a_ ∈ _A_<sup>old</sup> \{ _d_ } to alternative _d_ . Then with (4.6.12) and (4.6.14), we get: _c(_ 1 _), . . . , c(n_ − 1 _), g_ is a path from alternative _a_ to alternative _g_ ∈ _K_ with the same strength. Therefore, 



Suppose _c(_ 1 _), . . . , c(n)_ ∈ _A_<sup>new</sup> is the strongest path from alternative _a_ ∈ _A_<sup>new</sup> \ _K_ to alternative _g_ ∈ _K_ . Then with (4.6.12) and (4.6.14), we get: _c(_ 1 _), . . . , c(m_ − 1 _), d,_ where _c(m)_ is the first occurrence of an alternative of the set _K_ , was a path from alternative _a_ to alternative _d_ with at least the same strength. Therefore, 



Suppose _c(_ 1 _), . . . , c(n)_ ∈ _A_<sup>old</sup> was the strongest path from alternative _d_ to alternative _b_ ∈ _A_<sup>old</sup> \{ _d_ } _._ Then with (4.6.13) and (4.6.14), we get: _g, c(_ 2 _), . . . , c(n)_ is a path from alternative _g_ ∈ _K_ to alternative _b_ with the same strength. Therefore, 



Suppose _c(_ 1 _), . . . , c(n)_ ∈ _A_<sup>new</sup> is the strongest path from alternative _g_ ∈ _K_ to alternative _b_ ∈ _A_<sup>new</sup> \ _K_ . Then with (4.6.13) and (4.6.14), we get: _d, c(m_ + 1 _), . . . , c(n),_ 

123 

A new monotonic, clone-independent, reversal symmetric 

293 

where _c_ ( _m_ ) is the last occurrence of an alternative of the set _K_ , was a path from alternative _d_ to alternative _b_ with at least the same strength. Therefore, 



( _α)_ Suppose the strongest path _c(_ 1 _), . . . , c(n)_ ∈ _A_<sup>old</sup> from alternative _a_ ∈ _A_<sup>old</sup> \{ _d_ } to alternative _b_ ∈ _A_<sup>old</sup> \{ _a, d_ } did not contain alternative _d_ . Then with (4.6.14), we get: _c(_ 1 _), . . . , c(n)_ is still a path from alternative _a_ to alternative _b_ with the same strength. Therefore, _PD_<sup>new</sup> [ _a, b_ ] ∼<sup>≻</sup> _D PD_<sup>old[</sup><sup>_a, b_]</sup><sup>_._</sup> ( _β)_ Suppose the strongest path _c(_ 1 _), . . . , c(n)_ ∈ _A_<sup>old</sup> from alternative _a_ ∈ _A_<sup>old</sup> \{ _d_ } to alternative _b_ ∈ _A_<sup>old</sup> \{ _a, d_ } contained alternative _d_ . Then with (4.6.12), (4.6.13), and (4.6.14), we get: _c(_ 1 _), . . . , c(n),_ with alternative _d_ replaced by an arbitrarily chosen alternative _g_ ∈ _K_ , is still a path from alternative _a_ to alternative _b_ with the same strength. Therefore, _PD_<sup>new</sup> [ _a, b_ ] ∼<sup>≻</sup> _D PD_<sup>old[</sup><sup>_a, b_]</sup><sup>_._</sup> 

With ( _α)_ and ( _β)_ , we get 



( _γ )_ Suppose the strongest path _c(_ 1 _), . . . , c(n)_ ∈ _A_<sup>new</sup> from alternative _a_ ∈ _A_<sup>new</sup> \ _K_ to alternative _b_ ∈ _A_<sup>new</sup> \ _(K_ ∪{ _a_ } _)_ does not contain alternatives of the set _K_ . Then with (4.6.14), we get: _c_ (1),…, _c_ ( _n_ ) was a path from alternative _a_ to alternative _b_ with the same strength. Therefore, _P_<sup>old</sup> _D_<sup>[</sup><sup>_a_,</sup><sup>_b_]≻∼</sup> _D_<sup>_P_new</sup> _D_<sup>[</sup><sup>_a_,</sup><sup>_b_].</sup> 

( _δ)_ Suppose the strongest path _c(_ 1 _), . . . , c(n)_ ∈ _A_<sup>new</sup> from alternative _a_ ∈ _A_<sup>new</sup> \ _K_ to alternative _b_ ∈ _A_<sup>new</sup> \ _(K_ ∪{ _a_ } _)_ contains some alternatives of the set _K_ . Then with (4.6.12), (4.6.13), and (4.6.14), we get: _c_ (1),…, _c_ ( _s_ − 1), _d_ , _c_ ( _t_ +1),…, _c_ ( _n_ ), where _c_ ( _s_ ) is the first occurrence of an alternative of the set _K_ and _c_ ( _t_ ) is the last occurrence of an alternative of the set _K_ , was a path from alternative _a_ to alternative _b_ with at least the same strength. Therefore, _P_<sup>old</sup> _D_<sup>[</sup><sup>_a_,</sup><sup>_b_]≻∼</sup> _D_<sup>_P_new</sup> _D_<sup>[</sup><sup>_a_,</sup><sup>_b_].</sup> 

With ( _γ )_ and ( _δ)_ , we get 



Combining (4.6.15) and (4.6.16) gives 



Combining (4.6.17) and (4.6.18) gives 



Combining (4.6.19) and (4.6.20) gives 



With (4.6.21–4.6.23), we get (4.6.4–4.6.6). 

123 

M. Schulze 

294 

Part 1: Suppose _d_ ∈ _S_<sup>old</sup> . Then 



With (4.6.4) and (4.6.24), we get 



Since the binary relation _O_<sup>new</sup> , as defined in (2.2.1), is asymmetric and transitive, there must be an alternative _k_ ∈ _K_ with 



With (4.6.25) and (4.6.26), we get _k_ ∈ _S_<sup>new</sup> ∩ _K_ and, therefore, _S_<sup>new</sup> ∩ _K_ = ∅. Part 2: Suppose _d_ ∈ _/ S_<sup>old</sup> . Then 



With (4.6.4) and (4.6.27), we get 



With (4.6.28), we get: _S_<sup>new</sup> ∩ _K_ = ∅. With part 1 and part 2, we get (4.6.7). Part 3: Suppose _a_ ∈ _A_<sup>old</sup> \{ _d_ } and _a_ ∈ _S_<sup>old</sup> . Then 



With (4.6.5) and (4.6.29), we get 



With (4.6.6) and (4.6.30), we get 



With (4.6.31) and (4.6.32), we get: _a_ ∈ _S_<sup>new</sup> . 

Part 4: Suppose _a_ ∈ _A_<sup>old</sup> \{ _d_ } and _a_ ∈ _/ S_<sup>old</sup> . Then at least one of the following two statements must have been valid: 



123 

295 

A new monotonic, clone-independent, reversal symmetric 

With (4.6.5), (4.6.6), and (4.6.33), we get that at least one of the following two statements must be valid: 



With (4.6.34), we get: _a_ ∈ _/ S_<sup>new</sup> . With part 3 and part 4, we get (4.6.8). ⊓⊔ 

## 4.7 Smith 

The _Smith criterion_ and _Smith-IIA_ (where IIA means “independence of irrelevant alternatives”) say that _weak_ alternatives should have no impact on the result of the elections. 

Suppose: 



Then a _weak_ alternative in the Smith paradigm is an alternative _b_ ∈ _B_ 2. Adding or removing a weak alternative _b_ ∈ _B_ 2 should have no impact on the set _S_ of winners. 

**Definition** An election method satisfies the _Smith criterion_ if the following holds: Suppose (4.7.1) and (4.7.2). Then: 



_Remark_ If _B_ 1 consists of only one alternative _a_ ∈ _A_ , then this is the so-called _Condorcet criterion_ . If _B_ 2 consists of only one alternative _b_ ∈ _A_ , then this is the so-called _Condorcet loser criterion_ . 

**Claim** If ≻ _D_ satisfies (2.1.2), then the Schulze method, as defined in Sect. 2.2, satisfies the Smith criterion. 

_Proof_ The proof is trivial. Presumption (2.1.2) guarantees that any pairwise victory is stronger than any pairwise defeat. If _a_ ∈ _B_ 1 and _b_ ∈ _B_ 2, then already the link _ab_ is a path from alternative _a_ to alternative _b_ that consists only of a pairwise victory. On the other side, (4.7.2) says that there cannot be a path from alternative _b_ to alternative _a_ that contains no pairwise defeat. So already the link _ab_ is stronger than any path from alternative _b_ to alternative _a_ . ⊓⊔ 

123 

296 

M. Schulze 

**Definition** An election method satisfies _Smith-IIA_ if the following holds: Suppose (4.7.1) and (4.7.2). Then: 



**Claim** If ≻ _D_ satisfies (2.1.2), then the Schulze method, as defined in Sect. 2.2, satisfies Smith-IIA. 

_Proof_ We will prove (4.7.5)(a). The proof for (4.7.6) is analogous. 

(4.7.5)(b) follows directly from (4.7.4) and (4.7.5)(a). 

Part 1: Suppose _e, f_ ∈ _B_ 1. Suppose _ef_ ∈ _O_<sup>old</sup> . Then 



With (2.2.3), we get 



With (4.7.7) and (2.2.3), we get 



With (4.7.8) and (4.7.9), we get 





With (4.7.2), we get: Any path from alternative _e_ ∈ _B_ 1 to alternative _f_ ∈ _B_ 1 that contained alternative _d_ ∈ _B_ 2 necessarily contained a pairwise defeat. As it is not possible that the link _ef_ is a pairwise defeat and that simultaneously the link _fe_ is a pairwise defeat, max _D_ { ( _N_ [ _e_ , _f_ ], _N_ [ _f_ , _e_ ]), ( _N_ [ _f_ , _e_ ], _N_ [ _e_ , _f_ ]) } is stronger than any pairwise defeat [ because of (2.1.2) ]. Therefore, with (4.7.2) and (4.7.10), we get: The strongest path from alternative _e_ ∈ _B_ 1 to alternative _f_ ∈ _B_ 1 did not contain alternative _d_ ∈ _B_ 2. Therefore, 



As the elimination of alternative _d_ ∈ _B_ 2 only removes paths, we get 



123 

A new monotonic, clone-independent, reversal symmetric 

297 

With (4.7.11), (4.7.7), and (4.7.12), we get 





The _majority criterion for solid coalitions_ says that, when a majority of the voters strictly prefers every alternative of a given set of alternatives to every alternative outside this set of alternatives, then the winner must be chosen from this set. In short, an election method satisfies the _majority criterion for solid coalitions_ if the following holds: 

Suppose (4.7.1). Suppose ∥{ _v_ ∈ _V_ |∀ _a_ ∈ _B_ 1∀ _b_ ∈ _B_ 2 : _a_ ≻ _v b_ }∥ _> N /_ 2 _._ Then _S_ ⊆ _B_ 1. 

If _B_ 1 consists of only one alternative _a_ ∈ _A_ , then this is the so-called _majority criterion_ . If _B_ 2 consists of only one alternative _b_ ∈ _A_ , then this is the so-called _majority loser criterion_ . 

_Participation_ says that adding a list _W_ of ballots, on which every alternative of a given set of alternatives is strictly preferred to every alternative outside this set, must not hurt the alternatives of this set. In short, an election method satisfies _participation_ if the following holds: 

Suppose (4.7.1). Suppose ∀ _a_ ∈ _B_ 1∀ _b_ ∈ _B_ 2∀ _w_ ∈ _W_ : _a_ ≻ _w b_ . Suppose _V_<sup>new</sup> : = _V_<sup>old</sup> + _W_ . Then 



The Smith criterion implies the majority criterion for solid coalitions, the Condorcet criterion, and the Condorcet loser criterion. The majority criterion for solid coalitions implies the majority criterion and the majority loser criterion. The Condorcet criterion implies the majority criterion. The Condorcet loser criterion implies the majority loser criterion. Unfortunately, the Condorcet criterion is incompatible with the participation criterion (Moulin 1988). 

4.8 MinMax set 

For all ∅ = _B_ ⊊ _A,_ we define 



Suppose _βD_ := min _D_ { _�D (B)_ |∅̸ = _B_ ⊊ _A_ } _._ 

123 

M. Schulze 

298 

Suppose B _D_ := ∪{∅ = _B_ ⊊ _A_ | _�D_ ( _B_ ) ≈ _D βD_ } is the _MinMax set_ . Then B _D_ has the following properties: 

1. B _D_ = ∅. 

2. If B _D_ consists of only one alternative _a_ ∈ _A_ , then alternative _a_ is the unique Simpson–Kramer winner (i.e., that alternative _a_ ∈ _A_ with minimum max _D_ { _(N_ [ _b, a_ ] _, N_ [ _a, b_ ] _)_ | _b_ ∈ _A_ \{ _a_ }} _)_ . 

3. If _d_ ∈ B _D_ is replaced by a set of alternatives _K_ as described in (4.6.1–4.6.3), then B<sup>new</sup> _D_ = (B _D_ ∪ _K )_ \{ _d_ } _._ 

4. If _d_ ∈ _/_ B _D_ is replaced by a set of alternatives _K_ as described in (4.6.1–4.6.3), then B<sup>new</sup> _D_ = B _D_ . 

So, in some sense, the MinMax set B _D_ is a clone-proof generalization of the Simpson–Kramer winner. 

When we want primarily that the used election method is independent of clones and secondarily that the strongest link _ef_ , that is overruled when determining the winner, is minimized, then we have to demand that the winner is always chosen from the MinMax set B _D_ . 

**Claim** The Schulze method, as defined in Sect. 2.2, has the following properties: 



_Proof_ Suppose _a_ ∈ B _D_ . Then we get 



Suppose _b_ ∈ _/_ B _D_ . Then we get 



We will prove the following claims: 

Claim #1: _PD_ [ _b, a_ ] ∼<sup>≺</sup> _D βD._ Claim #2: _PD_ [ _a, b_ ] ∼<sup>≻</sup> _D γD._ 

With claim #1, claim #2, and (4.8.4), we get 



With (4.8.5), we get (4.8.1). With (4.8.1), we get (4.8.2). 

_Proof of claim #1:_ With (4.8.3) and (4.8.4), we get 



123 

A new monotonic, clone-independent, reversal symmetric 

299 

Suppose _c(_ 1 _), . . . , c(n)_ ∈ _A_ is the strongest path from alternative _b_ to alternative _a_ . Suppose _c(i)_ is the last alternative with _c(i)_ ∈ _/ B_ . Then we get ( _N_ [ _c(i), c(i_ + 1 _)_ ] _, N_ [ _c(i_ + 1 _), c(i)_ ]) ∼<sup>≺</sup> _D βD_ . Therefore, we get 



_Proof of claim #2:_ We can construct a path from alternative _a_ to alternative _b_ with a strength of at least _γD_ as follows: 

(1) We start with _E_ 1 : = { _a_ } and _i_ : = 1. Trivially, we get _b_ ∈ _/ E_ 1 and _PD_ [ _a, h_ ] ∼<sup>≻</sup> _D γD_ forall _h_ ∈ _E_ 1\ { _a_ } _._ 

- (2) At each stage, we consider the set _Bi_ : = _A_ \ _Ei_ . With _b_ ∈ _Bi_ and with (4.8.4), we get 

_�D(Bi )_ ≈ _D_ max _D_ { _(N_ [ _y, x_ ] _, N_ [ _x, y_ ] _)_ | _y_ ∈ _/ Bi , x_ ∈ _Bi_ } ∼<sup>≻</sup> _D γD._ (4.8.8) 

We choose _f_ ∈ _Ei_ and _g_ ∈ _Bi_ with 

_(N_ [ _f, g_ ] _, N_ [ _g, f_ ] _)_ ≈ _D_ max _D_ { _(N_ [ _y, x_ ] _, N_ [ _x, y_ ] _)_ | _y_ ∈ _/ Bi , x_ ∈ _Bi_ } ∼<sup>≻</sup> _D γD._ (4.8.9) 

We define _Ei_ +1 := _Ei_ ∪{ _g_ } _._ With _f_ ∈ _Ei ,_ with _PD_ [ _a, h_ ] ∼<sup>≻</sup> _D γD_ for all _h_ ∈ _Ei_ \ { _a_ } _,_ with _(N_ [ _f, g_ ] _, N_ [ _g, f_ ] _)_ ∼<sup>≻</sup> _D γD,_ and with _Ei_ +1 := _Ei_ ∪{ _g_ } _,_ we get 



(3) We repeat stage 2 with _i_ → _i_ +1, until _g_ ≡ _b_ . Therefore, we get 





## 4.9 Prudence 

_Prudence_ as a criterion for single-winner election methods has been popularized mainly by Arrow and Raynaud (1986). This criterion says that the strength _λD_ of the strongest link _ef_ , that is not supported by the binary relation _O_ , should be as small as possible. So _λD_ := max _D_ { _(N_ [ _e, f_ ] _, N_ [ _f, e_ ] _)_ | _ef_ ∈ _/ O_ } should be minimized. 

When there is a directed cycle _c(_ 1 _), . . . , c(n)_ ∈ _A_ with _c_ (1) ≡ _c_ ( _n_ ), then it is obvious that the strongest link, that is not supported by the binary relation _O_ , is at least as strong as the weakest link _c_ ( _i_ ), _c_ ( _i_ +1) of this directed cycle. So we get: 



123 

M. Schulze 

300 

As we have to make this consideration for all directed cycles, the maximum, that we can ask for, is the following criterion. 

**Definition** Suppose _λD_ ∈ N0 × N0 is the strength of the strongest directed cycle. 



Then an election method is _prudent_ if the following holds: 



**Claim** The Schulze method, as defined in Sect. 2.2, is prudent. 

_Proof_ The proof is trivial. With (2.2.4), we get: _ab_ ∈ _O_ , unless the link _ab_ is in a directed cycle that consists of links of which each is at least as strong as the link _ab_ . ⊓⊔ 

## **5 Comparison with other methods** 

Table 2 compares the Schulze method with its main contenders. Extensive descriptions of the different methods can be found in publications by Fishburn (1977), Nurmi (1987), Kopfermann (1991), Levin and Nalebuff (1995), and Tideman (2006). As most of these methods only generate a set _S_ of winners and don’t generate a binary relation _O_ , only that part of the different criteria is considered that refers to the set _S_ of winners. 

In terms of satisfied and violated criteria, that election method, that comes closest to the Schulze method, is Tideman’s ranked pairs method (Tideman 1987). The only difference is that the ranked pairs method doesn’t choose from the MinMax set B _D_ . 

The ranked pairs method works from the strongest to the weakest link. The link _xy_ is locked if and only if it doesn’t create a directed cycle with already locked links. Otherwise, this link is locked in its opposite direction. 

In Example 1, the ranked pairs method locks _db_ . Then it locks _cb_ . Then it locks _ac_ . Then it locks _ab_ , since locking _ba_ in its original direction would create a directed cycle with the already locked links _ac_ and _cb_ . Then it locks _cd_ . Then it locks _ad_ , since locking _da_ in its original direction would create a directed cycle with the already locked links _ac_ and _cd_ . 

The winner of the ranked pairs method is alternative _a_ ∈ _/_ B _D_ = { _d_ } _,_ because there is no locked link that ends in alternative _a_ . 

Although Tideman’s ranked pairs method is that election method that comes closest to the Schulze method in terms of satisfied and violated criteria, random simulations by Wright (2009) showed that that election method, that agrees the most frequently with the Schulze method, is the Simpson–Kramer method (Table 1). 

123 

A new monotonic, clone-independent, reversal symmetric 

301 

||nce Polynomial<br>runtime|Y|Y|Y|Y|Y|N|Y|N|Y|Y|Y|Y|Y|N|N||
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
||x set Prude|N|N|N|N|N|N|N|N|N|N|Y|Y|Y|N|N||
||pation MinMa|N|N|N|N|N|N|N|N|N|N|N|Y|N|N|N||
||ity Partici|N|N|Y|N|N|N|N|N|N|Y|N|N|N|N|N||
||rity Major<br>loser|Y|Y|Y|Y|Y|N|Y|Y|Y|N|Y|Y|N|Y|N||
||y for<br>Majo<br>alitions|Y|Y|N|Y|Y|Y|Y|Y|Y|Y|Y|Y|Y|Y|Y||
||rcet Majorit<br>solid co|Y|N|N|Y|Y|N|Y|Y|Y|N|Y|Y|N|Y|N||
||cet Condo<br>loser|Y|Y|Y|N|Y|N|Y|Y|Y|N|Y|Y|N|Y|N||
||IA Condor|Y|Y|N|N|Y|Y|N|Y|Y|N|Y|Y|Y|Y|Y||
||h Smith-I|N|N|N|N|Y|N|N|Y|N|N|Y|Y|N|Y|N||
||ce Smit|Y|N|N|N|Y|N|N|Y|Y|N|Y|Y|N|Y|N||
||onicity Independen<br>of clones|N|N|N|N|N|N|Y|N|N|N|Y|Y|N|N|N||
|ods|al<br>Monot<br>try|N|Y|Y|Y|Y|N|N|Y|N|Y|Y|Y|Y|Y|Y||
|on Meth|to Revers<br>symme|N|Y|Y|N|Y|N|N|Y|Y|N|Y|Y|N|Y|N||
|of Electi|bility Pare|Y|Y|Y|Y|Y|Y|Y|Y|Y|Y|Y|Y|Y|Y|Y||
|parison|Resolva|Y|Y|Y|Y|N|Y|Y|Y|Y|Y|Y|Y|r Y|N|Y|e|
|Com||||||||off|Young|||irs||Krame|||plianc<br>tion|
|**Table 2**||Baldwin|Black|Borda|Bucklin|Copeland|Dodgson|Instant run|Kemeny–|Nanson|Plurality|Ranked pa|Schulze|Simpson–|Slater|Young|Y=com<br>N=viola|



123 

M. Schulze 

302 

## **6 Discussion** 

Suppose _�D(a)_ := max _D_ { _(N_ [ _b, a_ ] _, N_ [ _a, b_ ] _)_ | _b_ ∈ _A_ \{ _a_ }} is the Simpson–Kramer score of alternative _a_ ∈ _A_ . Then the Simpson–Kramer method is defined as follows: 



Over a long period of time, this method was the most popular election method among Condorcet activists, because this method minimizes the number of overruled voters. However, a very serious problem of this method is that it is not independent of clones, because it can happen that, when alternative _a_ ∈ _A_ is replaced by a set of clones _K_ as described in (4.6.1–4.6.3), then the alternatives of the set _K_ disqualify each other in such a manner that for some alternative _b_ ∈ _A_ \{ _a_ }: 



To make the Simpson–Kramer method clone-proof, the concept of Simpson–Kramer scores has to be generalized from individual alternatives _a_ ∈ _A_ to sets of alternatives ∅ = _B_ ⊊ _A_ : 



We get 



The _�D_ scores are clone-proof because, when alternative _a_ ∈ _A_ is replaced by a set of clones _K_ , then we get for all ∅̸ = _B_ ⊊ _A_ : 



Suppose _βD_ := min _D_ { _�D (B)_ |∅̸ = _B_ ⊊ _A_ } and B _D_ := ∪{∅̸ = _B_ ⊊ _A_ | _�D (B)_ ≈ _D βD_ } _._ Then when we want primarily that the used election method is clone-proof and secondarily that it minimizes the number of overruled voters, then the maximum, that we can ask for, is 



In this article, we propose a new single-winner election method ( _Schulze method_ ) that is clone-proof (Sect. 4.6) and that always chooses from the MinMax set B _D_ (Sect. 4.8). The latter property is the most characteristic property of the Schulze method, since this is the first time that an election method with this property is proposed. 

The Schulze method also satisfies many other criteria; some of them are also satisfied by the Simpson–Kramer method, like the Pareto criterion (Sect. 4.3), resolvability 

123 

A new monotonic, clone-independent, reversal symmetric 

303 

(Sect. 4.2), monotonicity (Sect. 4.5), and prudence (Sect. 4.9); some of them are violated by the Simpson–Kramer method, like the Smith criterion (Sect. 4.7) and reversal symmetry (Sect. 4.4). Because of this large number of satisfied criteria, we consider the Schulze method to be a promising alternative to the Simpson–Kramer method for actual implementations, especially when manipulation through clones or weak alternatives is an issue. 

**Acknowledgements** I want to thank Lowell Bruce Anderson, Blake Cretney, Jobst Heitzig, Rob Lanphier, Rob LeGrand, Andrew Myers, Norman Petry, Nic Tideman, Kevin Venzke, Douglas R. Woodall, and Thomas Zavist for fruitful discussions. 

## **References** 

Arrow KJ, Raynaud H (1986) Social choice and multicriterion decision-making. MIT Press, Cambridge Börgers C (2009) Mathematics of social choice: voting, compensation, and division. SIAM, Philadelphia Camps R, Mora X, Saumell L (2008) A continuous rating method for preferential voting. Working paper Fishburn PC (1977) Condorcet social choice functions. SIAM J Appl Math 33:469–489 Floyd RW (1962) Algorithm 97 (Shortest Path). Commun ACM 5:345 

Kopfermann K (1991) Mathematische Aspekte der Wahlverfahren. BI-Verlag, Mannheim Levin J, Nalebuff B (1995) An introduction to vote-counting schemes. J Econ Perspect 9:3–26 McCaffreyJD (2008) Testrun:groupdeterminationinsoftwaretesting.MSDNMagazine,Redmond,Washington 

Moulin H (1988) Condorcet’s principle implies the no show paradox. J Econ Theory 45:53–64 Nurmi HJ (1987) Comparing voting systems. Springer-Verlag, Berlin 

Rivest RL, Shen E (2010) An optimal single-winner preferential voting system based on game theory. Working paper 

Saari DG (1994) Geometry of voting. Springer-Verlag, Berlin 

Smith JH (1973) Aggregation of preferences with variable electorate. Econometrica 41:1027–1041 Stahl S, Johnson PE (2006) Understanding modern mathematics. Jones & Bartlett Publishing, Boston Tideman TN (1987) Independence of clones as a criterion for voting rules. Soc Choice Welf 4:185–206 Tideman TN (2006) Collective decisions and voting: the potential for public choice. Ashgate Publishing, Burlington 

Wright B (2009) Objective measures of preferential ballot voting systems. Doctoral dissertation, Duke University, Durham, North Carolina 

Yue A, Liu W, Hunter A (2007) Approaches to constructing a stratified merged knowledge base. Symbolic and quantitative approaches to reasoning with uncertainty, 9th European Conference, ECSQARU 2007 

123 

