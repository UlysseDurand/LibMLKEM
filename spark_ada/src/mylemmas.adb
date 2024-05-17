
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body MyLemmas 
with 
   SPARK_Mode => On 
is

   -- Our Lemmas for the SPARK Proofs

   --  Returns the sign of a Big_Integer (<0, =0 or >0)
   function sign (A: Big_Integer) return Sig is
   (if A > 0 then Posi elsif A = 0 then Nul else Nega);

   --  Multiplication of two signs (the image of the multiplication on Big_Integers by the `sign` isomorphism)
   function "*" (A : Sig ; B : Sig) return Sig is
   (if A = Nul or B = Nul then Nul elsif (A = Posi and B = Posi) or (A = Nega and B = Nega ) then Posi else Nega);

   --  Procedure that proves that a number is prime, from SPARK User's Guide - 7.9.3.2
   procedure Number_Is_Prime (N: Big_Natural) is null;


   --  If A mod B = 0 then there is k such that...
   function CorrespDividOne(A : Big_Integer; B : Big_Integer) return Big_Integer is 
   k : Big_Integer := A/B;
   begin 
      pragma Assert (In_Range(Interval'(- (abs A), abs A), k));
      pragma Assert (A = k * B);
      pragma Assert (sign(k) = sign(A) * sign(B));
      return k;
   end; 

   --  The other way
   function CorrespDividTwo(A : Big_Integer; B : Big_Integer) return Boolean is (True);

   -- If B divides A then B divides M*A
   function DivideMult(A : Big_Integer; B : Big_Integer; M : Big_Integer) return Boolean is 
      k1 : Big_Integer;
      k2 : Big_Integer;
   begin
      k1 := CorrespDividOne(A,B);
      pragma Assert (for some k in Interval'(-abs A, abs A) => ( k*B = A ));

      pragma Assert (In_Range (Interval'( -abs(A), abs(A) ), k1));
      k2 := k1*M;
      --  Multiplication is monotonic
      pragma Assert (In_Range (Interval'( -abs(M*A),abs(M*A)), k2));

      pragma Assert (for some k in Interval'(-abs (M * A), abs (M * A) ) => k * B = M * A);
      return True; 
   end;

   -- If B divides C and B divides D then B divides C + D
   function DivideAdd(B: Big_Integer; C: Big_Integer; D: Big_Integer) return Boolean is
   k1 : Big_Integer;
   k2 : Big_Integer; 
   Interv : Interval;
   begin
      k1 := CorrespDividOne(C,B);
      k2 := CorrespDividOne(D,B);

      Interv := (- abs (C+D), abs (C+D));
      -- k1+k2 has to be in Interv
      pragma Assert (In_Range(Interv, k1+k2));

      pragma Assert (B * (k1 + k2) = C + D);
      pragma Assert (for some k in Interv => (C + D = k * B));
      pragma Assert (CorrespDividTwo(C + D, B));
      return True;
   end; 

   function ext_gcd (A: Big_Natural ; B: Big_Natural) return Ext_cd is
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
         Res := (0,1,B);
      else 
         --  The subcall
         LilGcd := ext_gcd(B, R);
         --  The Postconditions of the subcall
         pragma Assert (B * LilGcd.U + R * LilGcd.V = LilGcd.D);
         pragma Assert (B mod LilGcd.D = 0);
         pragma Assert (R mod LilGcd.D = 0);

         U := LilGcd.V;
         V := LilGcd.U - M * LilGcd.V;
         D := LilGcd.D;

         pragma Assert (By (B * M mod D = 0, DivideMult(B, D, M) ));

         pragma Assert (By (A mod D = 0, DivideAdd(D, B * M, R)) );

         pragma Assert (B mod D = 0);
         --  Some calculus shows it
         pragma Assert (A * U + B * V = D);
         --  Finally we have our conditions
         Res := (U,V,D);
      end if;
      return Res;
   end;

   function Lemma_prime_divides_product (A : Big_Natural; B : Big_Natural; P : Big_Natural) return Boolean is
   begin
      return True;
   end;
end MyLemmas;