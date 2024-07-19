package body RefMLKEM 
    with SPARK_Mode => On
is
    package body ZqRef is

        function "**" (A : T_Ref ;
                       B : Big_Natural) return T_Ref
        is
            (if B = 0 then 1 else A * (A ** (B - 1)));

        function Lemma_Pow_Def (A : T_Ref;
                                B : Big_Natural) return Boolean is (True);

    end ZqRef;

   function NTT_Very_Inner_Ref (E : Array_Zq; Psi : T_Ref; J : Index_Ref; I : Index_Ref) return T_Ref 
   is (Psi ** (2 * To_Big (I) * To_Big (J) + To_Big (I) ) * E (I));
   --  Array_Generator_Very_Inner (E, Psi, J) (I) = NTT_Very_Inner_Ref (E, Psi, J, I)
   function NTT_Inner_Ref (E : Array_Zq; Psi : T_Ref; Useless : Index_Ref; J : Index_Ref) return T_Ref
   is (Generic_Sum.Sum (Array_Generator_Very_Inner (E, Psi, J)));
   --  Array_Generator_Inner (E, Psi, 0) (J) = NTT_Inner_Ref (E, Psi, 0, J)
   function NTT_Ref (E : Array_Zq; Psi : T_Ref) return Array_Zq
   is (Array_Generator_Inner (E, Psi, 0));
end RefMLKEM;
