
with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Big_Intervals; use SPARK.Big_Intervals;
package MyLemmas
with
    SPARK_Mode => On
is
   --  Our lemmas for the SPARK proof

   --  To make proofs according to the sign of a Big_Integer
   type Sig is (Posi, Nul , Nega);

   function sign (A: Big_Integer) return Sig;

   function "*" (A : Sig ; B : Sig) return Sig;


   -- Prove a number is prime
   function Is_Prime (N : Big_Natural) return Boolean is
   (N > 1 and then (
      for all J in Interval'(2,N) => ( N mod J /= 0)
   ));

   --  === Correspondance between definitions of one number divides another ===
   function CorrespDividOne(A : Big_Integer; B : Big_Integer) return Big_Integer with
      Ghost,
      Pre => B /= 0 and then (A mod B = 0),
      Post =>  
         In_Range(Interval'(-abs A, abs A), CorrespDividOne'Result) and 
         (A = CorrespDividOne'Result * B) and
         sign(CorrespDividOne'Result) = (sign(A) * sign(B));

   function CorrespDividTwo(A : Big_Integer; B : Big_Integer) return Boolean with
      Ghost,
      Pre => B /= 0 and then (for some k in Interval'(-abs A, abs A) => (A = k * B)),
      Post => CorrespDividTwo'Result and A mod B = 0;
   --  ======
  

   -- === Properties of divisibility ===
   --  if B divides A then B divides A * M
   function goodDivideMult(A : Big_Integer; B : Big_Integer; M : Big_Integer) return Boolean with
      Ghost,
      Pre => B /= 0 and then(A mod B = 0),
      Post => goodDivideMult'Result and A * M mod B = 0;

   -- if B divides C and B divides D then B divides C + D
   function goodDivideAdd(B: Big_Integer; C: Big_Integer; D: Big_Integer) return Boolean with
      Ghost,
      Pre => B /= 0 and then(C mod B = 0 and D mod B =0),
      Post => goodDivideAdd'Result and (C + D) mod B = 0;

   --  ======


   --  === for A and B, there are U, V, D such that A * U + B * V = D and D divides A and D divides B ===
   type Ext_cd is record 
      U : Big_Integer;
      V : Big_Integer;
      D : Big_Natural;
   end Record;

   --  Always Return annotation is needed to make SPARK verify that this function terminates.
   function ext_gcd (A : Big_Natural; B : Big_Natural) return Ext_cd
   with
      Ghost,
      Annotate => (GNATprove, Always_Return),
      Subprogram_Variant => (Decreases => B),
      Pre => B /= 0,
      Post =>
         ext_gcd'Result.D > 0 and
         A * ext_gcd'Result.U + B * ext_gcD'Result.V = ext_gcd'Result.D and
         A mod ext_gcd'Result.D = 0 and
         B mod ext_gcd'Result.D = 0;
   --  ======

   -- === If P prime divides A * B then either P divides A either it divides B ===
   function Lemma_prime_divides_product
      (
         A : Big_Natural ;
         B : Big_Natural ;
         P : Big_Natural 
      )
   return Boolean with
      Ghost,
      Global => null,
      Pre =>
         Is_Prime(P) and then (
            (A * B) mod P = 0
         ),
      Post =>
         Lemma_prime_divides_product'Result and 
         (
            A mod P = 0 or 
            B mod P = 0
         );
   -- ======
end MyLemmas;