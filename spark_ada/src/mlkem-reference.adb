
with SumGen;

package body MLKEM.Reference
   with SPARK_Mode => On 
is

   function NTT_Ref (A : in Poly_Zq) return NTT_Poly_Zq
   is
      A_HAT : NTT_Poly_Zq;

      --  Here, A is the constant parameter P1 and I the constant parameter P2
      function The_Func (A : Poly_Zq;
                         I : Index_256; 
                         J : Index_256) return T is
         (Psi ** (2 * Index_256_To_Big (I) * Index_256_To_Big (J) + Index_256_To_Big (I)) * A (I));

      package My_Sum is new SumGen.Generic_Sum (Poly_Zq, Index_256, Index_256, T, T(0), The_Func);
   begin
      for I in Index_256'Range loop
         --  A and J stay constant here, we sum over the last parameter of The_Func
         A_HAT (I) := (My_Sum.Sum (A, I, 0, Index_256'Last));
      end loop;
      return A_HAT;
   end NTT_Ref;

end MLKEM.Reference;