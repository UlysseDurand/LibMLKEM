with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body MyLemmas 
with 
   SPARK_Mode => On 
is

   --  Our Lemmas for the SPARK Proofs

   --  Returns the sign of a Big_Integer (<0, =0 or >0)
   function sign (A: Big_Integer) return Sig 
   is
      (if A > 0 then Posi elsif A = 0 then Nul else Nega);

   --  Multiplication of two signs (the image of the multiplication on Big_Integers by the `sign` functor)
   function "*" (A : Sig; 
                 B : Sig) return Sig 
   is
      (if A = Nul or B = Nul then Nul 
       elsif (A = Posi and B = Posi) or (A = Nega and B = Nega ) then Posi 
       else Nega);

   --  If A mod B = 0 then there is k such that k * B = A. We add that k is between -  abs A and abs A
   function CorrespDividOne (A : Big_Integer;
                             B : Big_Integer) return Big_Integer 
   is 
      k : Big_Integer := A / B;
   begin 
      pragma Assert (In_Range (Interval' (- (abs A), abs A), k));
      pragma Assert (A = k * B);
      pragma Assert (sign (k) = sign (A) * sign (B));
      return k;
   end; 

   --  The other way
   function CorrespDividTwo (A : Big_Integer; B : Big_Integer) return Boolean 
   is 
      (True);

   --  If B divides A then B divides M * A
   function DivideMult (A : Big_Integer; B : Big_Integer; M : Big_Integer) return Boolean is 
      k1 : Big_Integer;
      k2 : Big_Integer;
   begin
      k1 := CorrespDividOne (A, B);
      pragma Assert (for some k in Interval' (- abs A, abs A) => (k * B = A));

      pragma Assert (In_Range (Interval' (- abs (A), abs (A)), k1));
      k2 := k1 * M;
      --  Multiplication is monotonic
      pragma Assert (In_Range (Interval' ( - abs (M * A), abs (M * A)), k2));

      pragma Assert (for some k in Interval' (- abs (M * A), abs (M * A) ) => k * B = M * A);
      return True; 
   end;

   --  If B divides C and B divides D then B divides C + D
   function DivideAdd (B : Big_Integer;
                       C : Big_Integer;
                       D : Big_Integer) return Boolean 
   is
      k1 : Big_Integer;
      k2 : Big_Integer; 
      Interv : Interval;
   begin
      k1 := CorrespDividOne (C, B);
      k2 := CorrespDividOne (D, B);

      Interv := (- abs (C + D), abs (C + D));
      --  k1 + k2 has to be in Interv
      pragma Assert (In_Range (Interv, k1 + k2));

      pragma Assert (B * (k1 + k2) = C + D);
      pragma Assert (for some k in Interv => (C + D = k * B));
      pragma Assert (CorrespDividTwo (C + D, B));
      return True;
   end; 

   function ext_gcd ( A: Big_Natural;
                      B: Big_Natural) return Ext_cd 
   is
      M : Big_Natural := A / B;
      R : Big_Natural := A mod B;
      LilGcd : Ext_cd ;
      U : Big_Integer;
      V : Big_Integer;
      D : Big_Natural;
      Res : Ext_cd;
   begin
      pragma Assert (A = B * M + R);
      if (R = 0) then
         --  The basic case has such U, V, D
         Res := (0, 1, B);
      else 
         --  The subcall
         LilGcd := ext_gc (B, R);
         --  The Postconditions of the subcall
         pragma Assert (B * LilGcd.U + R * LilGcd.V = LilGcd.D);
         pragma Assert (B mod LilGcd.D = 0);
         pragma Assert (R mod LilGcd.D = 0);

         U := LilGcd.V;
         V := LilGcd.U - M * LilGcd.V;
         D := LilGcd.D;

         pragma Assert (By (B * M mod D = 0, DivideMult (B, D, M)));

         pragma Assert (By (A mod D = 0, DivideAdd (D, B * M, R)));

         pragma Assert (B mod D = 0);
         --  Some calculus shows it
         pragma Assert (A * U + B * V = D);
         --  Finally we have our conditions
         Res := (U, V, D);
      end if;
      return Res;
   end;


   --  If P prime divides A * B then P divides A or P divides B
   function Lemma_prime_divides_product (A : Big_Natural; 
                                         B : Big_Natural; 
                                         P : Big_Natural) return Boolean
   is
      TheGcd : Ext_cd;
      U : Big_Integer;
      V : Big_Integer;
      D : Big_Integer;

      --  k * P = A * B
      k : Big_Integer := CorrespDividOne (A * B, P);
   begin

      --  The preconditions of the lemma
      pragma Assert (Is_Prime (P));
      pragma Assert ((A * B) mod P = 0);

      --  A * U + P * V = D, D divides A and D divides P
      TheGcd := ext_gcd (A, P);
      U := TheGcd.U;
      V := TheGcd.V;
      D := TheGcd.D;

      --  We will show that if P doesn't divide A then it divides B
      if A mod P /= 0 then

         --  As P prime and D divides P then D = 1 or D = P
         --  But if P doesn't divide A then D cannot be P so D = 1 
         pragma Assert (D = 1);

         --  Some rewriting...
         pragma Assert (A * U + P * V = 1 );
         pragma Assert (A * B * U + P * V * B = B);
         pragma Assert (k * P * U + P * V * B = B);

         --  We prove the preconditions of CorrespDividTwo
         pragma Assert (P * (k * U + V * B) = B);
         pragma Assert (In_Range (Interval' (- abs B, abs B) , k * U + V * B ));

         --  Now we know P divides P
         pragma Assert (CorrespDividTwo (B, P));
         pragma Assert (B mod P = 0);
      end if;

      --  We have our posticondition
      pragma Assert (A mod P = 0 or B mod P = 0);
      return True;
   end;
end MyLemmas;