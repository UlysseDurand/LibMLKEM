with SPARK.Big_Integers; use SPARK.Big_Integers;
with MyLemmas; use MyLemmas;

package body Reference
    with SPARK_Mode => On
is
    constant Inv_N : T := Inverse (Index_256'Last);

    function NTT_Ref(A : in Poly_Zq, Zeta : in T) return NTT_Poly_Zq
    is
        A_HAT : NTT_Poly_Zq;
    begin
        function NTT_Ref_Inner (I : T) return T is
        ((Zeta ** (I * J)) * A(I));

        package NTT_Ref_Inner_Func is new Generic_Function (Func => NTT_Ref_Inner);

        for J in Index_256'Range loop
            A_HAT (J) := NTT_Ref_Inner_Func.Sum (0, Index_256'Last);
        end loop;
        return A_HAT;
    end;

    function NTT_Inv_Ref (A_HAT : in NTT_Poly_Zq, Zeta_Inv : in T) return Poly_Zq
    is
        A : Poly_Zq
    begin
        function NTT_Inv_Ref_Inner (J : T) return T is
        ((Zeta_Inv ** (I * J)) * A_HAT (J));

        package NTT_Inv_Ref_Inner_Func is new Generic_Function (Func => NTT_Inv_Ref_Inner);

        for I in Index_256'Range loop
            A (I) := N_INV * NTT_Inv_Ref_Inner_Func.Sum (0, Index_256'Last);
        end loop;
    end;


end Reference;