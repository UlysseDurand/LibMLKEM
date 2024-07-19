
with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body SumGen 
    with SPARK_Mode => On
is

    function Is_Pow_Of_Two (A : Positive) return Boolean
    is
        Res : Boolean;
    begin
        if A = 1 then
            Res := True;
        else
            pragma Assert (A / 2 >= 1);
            Res := A > 1 and then (A mod 2 = 0 and Is_Pow_Of_Two (A / 2));
        end if;
        pragma Assert (Res = (A = 1 or (A > 1 and then (A mod 2 = 0 and Is_Pow_Of_Two (A / 2)))));
        return Res;
    end Is_Pow_Of_Two;

    package body Sum_On_Array is 

        function Cut_Last (A : ArrayType) return ArrayType
        is
            Res : ArrayType (A'First .. A'Last - 1) with Relaxed_Initialization;
        begin
            for I in A'First .. A'Last - 1 loop
                Res (I) := A (I);
                pragma Loop_Invariant (for all J in A'First .. I => (
                                            Res(J)'Initialized and
                                            Res(J) = A(J)
                                       ));
            end loop;
            pragma Assert (for all J in A'First .. A'Last - 1 => (Res (J) = A (J)));
            return Res;
        end Cut_Last;

        function "+" (F : ArrayType;
                      G : ArrayType) return ArrayType
        is
            Res : ArrayType (F'Range) with Relaxed_Initialization;
        begin
            for I in F'Range loop
                Res (I) := F (I) + G (I);
                pragma Loop_Invariant (for all J in F'First .. I => 
                                        Res(J)'Initialized and then 
                                        (Res (J) = F (J) + G (J)));
            end loop;
            pragma Assert (for all J in F'Range => Res (J) = F (J) + G (J));
            return Res;
        end "+";

        function Sum (A : ArrayType) return ElementType
        is
            (if A'Length = 0 then 0 elsif A'Length = 1 then A (A'First) else Sum (Cut_Last (A)) + A (A'Last));


        function Lemma_Add_Associative (A : ElementType;
                                        B : ElementType;
                                        C : ElementType) return Boolean
        is (True);

        function Lemma_Add_Commutative (A : ElementType;
                                        B : ElementType) return Boolean
        is (True);

        function Lemma_Mult_Add_Distributive (A : ElementType;
                                              B : ElementType;
                                              C : ElementType) return Boolean
        is 
        begin
            pragma Assume (A * (B + C) = A * B + A * C);
            return True;
        end;

        function Extract_Even (F : ArrayType) return ArrayType
        is 
            Res : ArrayType (0 .. IndexRange (F'Length / 2 - 1)) with Relaxed_Initialization;
        begin
            for I in 0 .. (F'Length / 2 - 1) loop
                Res (IndexRange (I)) := F (IndexRange (2 * I));
                pragma Loop_Invariant (for all J in 0 .. I => 
                    Res (IndexRange (J))'Initialized and
                    Res (IndexRange (J)) = F (IndexRange (2 * J))
                );
            end loop;
            return Res;
        end Extract_Even;

        function Extract_Odd (F : ArrayType) return ArrayType
        is 
            Res : ArrayType (0 .. IndexRange (F'Length / 2 - 1)) with Relaxed_Initialization;
        begin
            for I in 0 .. (F'Length / 2 - 1) loop
                Res (IndexRange (I)) := F (IndexRange (2 * I + 1));
                pragma Loop_Invariant (for all J in 0 .. I => 
                    Res (IndexRange (J))'Initialized and
                    Res (IndexRange (J)) = F (IndexRange (2 * J + 1))
                );
            end loop;
            return Res;
        end Extract_Odd;

        function Lemma_Split_Odd_Even (A : ArrayType) return Boolean
        is
        begin
            if (A'Length = 2) then
                pragma Assert (Extract_Even (A)'Length = 1);
                pragma Assert (Extract_Even (A)'Last = 0);
                pragma Assert (Sum (Extract_Even (A)) = Extract_Even (A)(Extract_Even (A)'Last));
                pragma Assert (Sum (Extract_Even (A)) = A (0));
                pragma Assert (Sum (A) = Sum (Extract_Even (A)) + Sum (Extract_Odd (A)));
            else
                declare
                    pragma Assert (A'Length > 2);
                    A_Shorter : ArrayType := Cut_Last (Cut_Last (A));
                    Induction_Hypothesis : Boolean := Lemma_Split_Odd_Even (A_Shorter);
                    Even_A : ArrayType := Extract_Even (A);
                    Odd_A : ArrayType := Extract_Odd (A);
                    Even_A_Shorter : ArrayType := Extract_Even (A_Shorter);
                    Odd_A_Shorter : ArrayType := Extract_Odd (A_Shorter);
                begin
                    pragma Assert (By (Sum (A_Shorter) = Sum (Even_A_Shorter) + Sum (Odd_A_Shorter), Induction_Hypothesis));

                    --  We prove Sum (Even_A) = Sum(Even_A_Shorter) + A (A'Last - 1)
                    pragma Assert (for all I in Even_A_Shorter'First .. Even_A_Shorter'Last => (
                        Cut_Last (Even_A) (I) = Even_A_Shorter (I)
                    ));
                    pragma Assert (Cut_Last (Even_A)'First = Even_A_Shorter'First);
                    pragma Assert (Cut_Last (Even_A)'Last = Even_A_Shorter'Last);
                    pragma Assert (Cut_Last (Even_A) = Even_A_Shorter);
                    pragma Assert (By (
                        Sum (Cut_Last (Even_A)) = Sum (Even_A_Shorter), 
                        Lemma_Sum_Extensional (Cut_Last (Even_A), Even_A_Shorter)
                    ));
                    pragma Assert (Even_A (Even_A'Last) = A (A'Last - 1));
                    pragma Assert (Sum (Even_A) = Sum (Even_A_Shorter) + A (A'Last - 1));

                    --  We prove Sum (Odd_A) = Sum (Odd_A_Shorter) + A (A'Last)
                    pragma Assert (for all I in Odd_A_Shorter'First .. Odd_A_Shorter'Last - 1 => (
                        Odd_A (I) = Odd_A_Shorter (I)
                    ));
                    pragma Assert (for all I in Odd_A_Shorter'First .. Odd_A_Shorter'Last => (
                        Cut_Last (Odd_A) (I) = Odd_A_Shorter (I)
                    ));
                    pragma Assert (Cut_Last (Odd_A)'First = Odd_A_Shorter'First);
                    pragma Assert (Cut_Last (Odd_A)'Last = Odd_A_Shorter'Last);
                    pragma Assert (Cut_Last (Odd_A) = Odd_A_Shorter);
                    pragma Assert (By (
                        Sum (Cut_Last (Odd_A)) = Sum (Odd_A_Shorter), 
                        Lemma_Sum_Extensional (Cut_Last (Odd_A), Odd_A_Shorter)
                    ));
                    pragma Assert (Odd_A (Extract_Odd (A)'Last) = A (A'Last));
                    pragma Assert (Sum (Odd_A) = Sum (Odd_A_Shorter) + A (A'Last));

                    -- We prove Sum (A) = Sum (A_Shorter) + A (A'Last - 1) + A (A'Last)
                    pragma Assert (Sum (A) = Sum (Cut_Last (A)) + A (A'Last));
                    pragma Assert (Sum (Cut_Last (A)) = Sum (A_Shorter) + A (A'Last - 1));
                    pragma Assert (Sum (A) = Sum (A_Shorter) + A (A'Last - 1) + A (A'Last));

                    pragma Assert (Sum (A) = ((Sum (Even_A_Shorter) + Sum (Odd_A_Shorter)) + A (A'Last - 1)) + A (A'Last));

                    --  All of the following just rearranges the terms to have
                    -- Sum (A) = (Sum (Even_A_Shorter) + A (A'Last - 1)) + (Sum (Even_A_Shorter) + A (A'Last))
                    pragma Assert (By (
                        ((Sum (Even_A_Shorter) + Sum (Odd_A_Shorter)) + A (A'Last - 1)) + A (A'Last) = (Sum (Even_A_Shorter) + (Sum (Odd_A_Shorter) + A (A'Last - 1))) + A (A'Last),
                        Lemma_Add_Associative (Sum (Even_A_Shorter), Sum (Odd_A_Shorter), A (A'Last - 1))
                    ));
                    pragma Assert (By (
                        (Sum (Even_A_Shorter) + (Sum (Odd_A_Shorter) + A (A'Last - 1))) + A (A'Last) = (Sum (Even_A_Shorter) + (A (A'Last - 1) + Sum (Odd_A_Shorter))) + A (A'Last),
                        Lemma_Add_Commutative (A (A'Last - 1), Sum (Odd_A_Shorter))
                    ));
                    pragma Assert (By (
                        (Sum (Even_A_Shorter) + (A (A'Last - 1) + Sum (Odd_A_Shorter))) + A (A'Last) = ((Sum (Even_A_Shorter) + A (A'Last - 1)) + Sum (Odd_A_Shorter)) + A (A'Last),
                        Lemma_Add_Associative (Sum (Even_A_Shorter), A (A'Last - 1), Sum (Odd_A_Shorter))
                    ));
                    pragma Assert (By (
                        ((Sum (Even_A_Shorter) + A (A'Last - 1)) + Sum (Odd_A_Shorter)) + A (A'Last) = (Sum (Even_A_Shorter) + A (A'Last - 1)) + (Sum (Odd_A_Shorter) + A (A'Last)),
                        Lemma_Add_Associative (Sum (Even_A_Shorter) + A (A'Last - 1), Sum (Odd_A_Shorter), A (A'Last))
                    ));
                    --
                    pragma Assert (Sum (A) = Sum (Even_A) + Sum (Odd_A));
                end;
            end if;
            return True;
        end Lemma_Split_Odd_Even;

        function Lemma_Sum_Extensional (A : ArrayType;
                                        B : ArrayType) return Boolean
        is
        begin
            if A'Length <= 1 then
                pragma Assert (Sum (A) = Sum (B));
            else
                declare
                    Induction_Hypothesis : Boolean := Lemma_Sum_Extensional (Cut_Last (A), Cut_Last (B));
                begin
                    pragma Assert (By (Sum (A) = Sum (B), Induction_Hypothesis));
                end;
            end if;
            return True;
        end Lemma_Sum_Extensional;

        function Scalar_Mult (A : ElementType;
                              B : ArrayType) return ArrayType
        is
            Res : ArrayType (B'Range) with Relaxed_Initialization;
        begin
            for I in B'Range loop
                Res (I) := A * B (I);
                pragma Loop_Invariant ( 
                    for all J in B'First .. I =>
                        Res (J)'Initialized and 
                        Res (J) = A * B (J)
                );
            end loop;
            return Res;
        end Scalar_Mult;

        function Lemma_Sum_Linear_Scal_Mult (A : ElementType;
                                             B : ArrayType;
                                             C : ArrayType) return Boolean
        is
        begin
            if B'Length = 0 then
                pragma Assert (Sum (C) = A * (Sum (B))); 
            else
                declare
                    Induction_Hypothesis : Boolean := Lemma_Sum_Linear_Scal_Mult (A, Cut_Last (B), Cut_Last (C));
                begin
                    pragma Assert (Sum (Cut_Last (C)) = A * Sum (Cut_Last (B)));
                    pragma Assert (C (C'Last) = A * B (B'Last));
                    pragma Assert (Sum (B) = Sum (Cut_Last (B)) + B (B'Last));
                    pragma Assert (Sum (C) = Sum (Cut_Last (C)) + C (C'Last));
                    pragma Assert (Sum (C) = A  * Sum (Cut_Last (B)) + C (C'Last));
                    pragma Assert (Sum (C) = A  * Sum (Cut_Last (B)) + A * B (B'Last));
                    pragma Assert (By (Sum (C) = A  * (Sum (Cut_Last (B)) + B (B'Last)), Lemma_Mult_Add_Distributive (A, Sum (Cut_Last (B)), B (B'Last))));
                    pragma Assert (Sum (C) = A * Sum (B));
                end;
            end if;
            return True;
        end Lemma_Sum_Linear_Scal_Mult;

        function InitialArray (Param1 : ArrayType;
                               Param2 : ElementType;
                               Param3 : IndexRange) return ArrayType
        is
            Res : ArrayType (Param1'Range) with Relaxed_Initialization;
        begin
            for I in Param1'Range loop
                Res (I) := Func (Param1, Param2, Param3, I);
                pragma Loop_Invariant (
                    for all J in Param1'First .. I => ( 
                        Res (J)'Initialized and 
                        Res(J) = Func (Param1, Param2, Param3, J)
                    )
                );
            end loop;
            return Res;
        end InitialArray;

    end Sum_On_Array;

end SumGen;