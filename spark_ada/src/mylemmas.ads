with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Big_Intervals; use SPARK.Big_Intervals;

package MyLemmas
with
    SPARK_Mode => On
is
   --  Our lemmas for some arithmetics on Big_Integers 

   --  To make proofs according to the sign of a Big_Integer
   type Sig is (Posi, Nul , Nega);

   function sign (A : Big_Integer) return Sig;

   function "*" (A : Sig ;
                 B : Sig) return Sig;

   --  Test if a number is prime
   function Is_Prime (N : Big_Natural) return Boolean 
   is
      (N > 1 and then (for all J in Interval'(2, N - 1) => (N mod J /= 0)));

   --  Here we give the lemmas to go from one definition to the other of one number divides another
   --  Indeed, B divides A if and only if A mod B = 0 if and only if exists K such that A = K * B
   --  As we can only use `for some` on bounded values, we add the fact that K is between - abs A and abs A 
   function Corresp_Divid_One (A : Big_Integer; 
                               B : Big_Integer) return Big_Integer 
      with Ghost,
           Pre => B /= 0 and then (A mod B = 0),
           Post =>  
              In_Range  (Interval'(- abs A, abs A), Corresp_Divid_One'Result) and 
              (A = Corresp_Divid_One'Result * B) and
              --  We add this postcondition on signs to help the proofs
              sign (Corresp_Divid_One'Result) = (sign (A) * sign (B));

   function Corresp_Divid_Two (A : Big_Integer;
                               B : Big_Integer) return Boolean 
      with Ghost,
           Pre => B /= 0 and then (for some K in Interval'(- abs A, abs A) => (A = K * B)),
           Post => Corresp_Divid_Two'Result and A mod B = 0;
  

   --  Here are some properties about divisibility
   --  If B divides A then B divides A * M
   function Divide_Mult (A : Big_Integer; 
                         B : Big_Integer; 
                         M : Big_Integer) return Boolean 
      with Ghost,
           Pre => B /= 0 and then (A mod B = 0),
           Post => Divide_Mult'Result and A * M mod B = 0;

   --  If B divides C and B divides D then B divides C + D
   function Divide_Add (B : Big_Integer; 
                        C : Big_Integer; 
                        D : Big_Integer) return Boolean 
      with Ghost,
           Pre => B /= 0 and then (C mod B = 0 and D mod B =0),
           Post => Divide_Add'Result and (C + D) mod B = 0;


   --  For A and B, there are U, V, D such that A * U + B * V = D and D divides A and D divides B 
   --  Ext_cd stands for extanded common divisor
   type Ext_cd is record 
      U : Big_Integer;
      V : Big_Integer;
      D : Big_Natural;
   end Record;

   --  This is an implementation and proof of the Euclid algorithm
   --  Still, we don't prove that the resulting D is the greatest of the common divisors 
   function Ext_gcd (A : Big_Natural;
                     B : Big_Natural) return Ext_cd
      with
         --  Always_Return annotation is needed to make SPARK verify that this function terminates.
         Annotate => (GNATprove, Always_Return),
         --  We know the recurive function terminates because B in the subcall is strictly less than the initial B
         Subprogram_Variant => (Decreases => B),
         Pre => B /= 0,
         Post =>
            Ext_gcd'Result.D > 0 and
            A * Ext_gcd'Result.U + B * Ext_gcd'Result.V = Ext_gcd'Result.D and
            A mod Ext_gcd'Result.D = 0 and
            B mod Ext_gcd'Result.D = 0;

   --  If P prime divides A * B then either P divides A either it divides B
   function Lemma_Prime_Divides_Product (A : Big_Natural; 
                                         B : Big_Natural; 
                                         P : Big_Natural) return Boolean 
      with Ghost,
           Global => null,
           Pre =>
              Is_Prime (P) and then ((A * B) mod P = 0),
           Post =>
              Lemma_Prime_Divides_Product'Result and
              (A mod P = 0 or B mod P = 0);

end MyLemmas;