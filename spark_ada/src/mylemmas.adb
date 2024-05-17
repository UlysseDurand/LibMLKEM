
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body MyLemmas 
with 
   SPARK_Mode => On 
is

   -- Our Lemmas for the SPARK Proofs

   function sign (A: Big_Integer) return Sig is
   (if A > 0 then Posi elsif A = 0 then Nul else Nega);

   function "*" (A : Sig ; B : Sig) return Sig is
   (if A = Nul or B = Nul then Nul elsif (A = Posi and B = Posi) or (A = Nega and B = Nega ) then Posi else Nega);

   --  function givesBigInterval (A : Big_Integer ; B : Big_Integer) return Interval is
   --  begin
   --     if A < B then 
   --        return (A,B); 
   --     else 
   --        return (B,A); 
   --     end if;
   --  end;

   --  procedure Number_Is_Prime (N: Big_Natural) is
   --  begin
   --     null;
   --  end Number_Is_Prime;

   function obviousComp(A : Big_Integer; B : Big_Integer) return Boolean is
   begin
      return True;
   end;

   function CorrespDividOne(A : Big_Integer; B : Big_Integer) return Big_Integer is 
   k : Big_Integer := A/B;
   begin 
      pragma Assert (k <= abs A);
      pragma Assert (k >= - (abs A));
      pragma Assert (By(
         In_Range(Interval'(- (abs A), abs A), k),
         k <= abs A and k >= - (abs A))
      );
      pragma Assert (A = k * B);
      pragma Assert (sign(k) = sign(A) * sign(B));
      return k;
   end; 

   function CorrespDividTwo(A : Big_Integer; B : Big_Integer) return Boolean is
   begin
      null;
   return True; end; 

   -- If B divides A then B divides M*A
   function goodDivideMult(A : Big_Integer; B : Big_Integer; M : Big_Integer) return Boolean is 
      k1 : Big_Integer;
      k2 : Big_Integer;
   begin
      k1 := CorrespDividOne(A,B);
      pragma Assert (for some k in Interval'(-abs A, abs A) => ( k*B = A ));

      pragma Assert (In_Range (Interval'( -abs(A), abs(A) ), k1));
      k2 := k1*M;
      pragma Assert (In_Range (Interval'( -abs(M*A),abs(M*A)), k2));

      pragma Assert (for some k in Interval'(-abs (M * A), abs (M * A) ) => k * B = M * A);
      return True; 
   end;

   -- If B divides C and B divides D then B divides C + D

   function goodDivideAdd(B: Big_Integer; C: Big_Integer; D: Big_Integer) return Boolean is
   k1 : Big_Integer;
   k2 : Big_Integer; 
   Interv : Interval;
   begin
      k1 := CorrespDividOne(C,B);
      k2 := CorrespDividOne(D,B);

      Interv := (- abs (C+D), abs (C+D));

      pragma Assert (if (k1 >= 0 and k2 >= 0) or (k1 <= 0 and k2 <= 0) then (In_Range(Interv, k1 + k2)));

      pragma Assert (By( (if (C >= 0 and B >= 0) or (C <= 0 and B <= 0) then k1 >= 0), k1 = CorrespDividOne(C, B)));
      pragma Assert (By( (if (C >= 0 and B <= 0) or (C <= 0 and B >= 0) then k1 <= 0), k1 = CorrespDividOne(C, B)));
      pragma Assert (By( (if (D >= 0 and B >= 0) or (D <= 0 and B <= 0) then k2 >= 0), k2 = CorrespDividOne(D, B)));
      pragma Assert (By( (if (D >= 0 and B <= 0) or (D <= 0 and B >= 0) then k2 <= 0), k2 = CorrespDividOne(D, B)));

      pragma Assert (if (k1 >= 0 and k2 <= 0) then (In_Range(Interv, k1 + k2)));
      pragma Assert (In_Range(Interv, k1+k2));
      pragma Assert (B * (k1 + k2) = C + D);
      pragma Assert (for some k in Interv => (C + D = k * B));
      --  pragma Assert (By(CorrespDividTwo(C + D, B), k = k1+k2));
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
         Res := (0,1,B);
      else 
         LilGcd := ext_gcd(B, R);
         pragma Assert (B * LilGcd.U + R * LilGcd.V = LilGcd.D);
         pragma Assert (B mod LilGcd.D = 0);
         pragma Assert (R mod LilGcd.D = 0);

         U := LilGcd.V;
         V := LilGcd.U - M * LilGcd.V;
         D := LilGcd.D;

         pragma Assume (B * M mod D = 0);

         pragma Assume (A mod D = 0);
         pragma Assert (B mod D = 0);
         pragma Assert (A * U + B * V = D);
         Res := (U,V,D);
      end if;
      return Res;
   end;

   --  function Lemma_prime_divides_product (A : Big_Natural; B : Big_Natural; P : Big_Natural) return Boolean is
   --  begin
   --     return True;
   --  end;
end MyLemmas;