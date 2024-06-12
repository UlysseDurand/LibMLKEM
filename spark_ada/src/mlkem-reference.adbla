--  This package has the mathematical references to all the mathematical function
--  we want our program to compute.

private
package MLKEM.Reference 
   with SPARK_Mode => On
is

   use Zq;

   --  This is a 256th root of the unity and its inverse 
   Psi : constant T := 17;
   Psi_Inv : constant T := 1175;

   function NTT_Ref (A : in Poly_Zq) return NTT_Poly_Zq
      with Ghost;

end MLKEM.Reference;