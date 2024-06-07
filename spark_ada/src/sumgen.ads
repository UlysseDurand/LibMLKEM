--  This requires the type returnType to have "+"
generic
    N : Integer;
package SumGen 
    with SPARK_Mode => On
is
    type IndexRange is range 0 .. N-1;
    type Partial is array (IndexRange) of Boolean;




    generic
        type Type1 is private;
        type Type2 is private;
        type IndexRange is range <>;
        type ReturnType is mod <>;
        Zero : ReturnType;
        with function Func (P1     : Type1;
                            P2     : Type2; 
                            J      : IndexRange) return ReturnType;

    package Generic_Sum 
        with SPARK_Mode => On
    is
        function Sum (P1 : Type1;
                      P2 : Type2;
                      A : IndexRange;
                      B : IndexRange) return ReturnType;

        function Lemma_Sum_Splitable (P1 : Type1;
                                      P2 : Type2;
                                      A : IndexRange; 
                                      B : IndexRange; 
                                      C : IndexRange) return Boolean
            with Pre => C > A and C <= B,
                Post => Lemma_Sum_Splitable'Result and
                        Sum (P1, P2, A, C - 1) + Sum (P1, P2, C, B) = Sum (P1, P2, A, C);
    end Generic_Sum;

    generic
        type elements is private:
        type indexGlobal is range <>;
        with 

    generic 
        type InType is private;
        type IntermediateType is private;
        type ReturnType is private;
        with function F (A : InType) return ReturnType;
        with function G (B : InType) return ReturnType;
    function Compose (A : InType) return ReturnType;

    generic
        Q : Integer;
        type ReturnType is mod Q;
    function To_Even (A : ReturnType) return ReturnType is
        (ReturnType (2) * A);

    generic
        Q : Integer;
        type ReturnType is mod Q;
    function To_Odd (A : ReturnType) return ReturnType is
        (ReturnType (2) * A + ReturnType (1));

    generic Generic_Lemma_Sum_Odd_Even
        type Type1 is private;
        type Type2 is private;
        type IndexRange is range <>;
        type ReturnType is mod <>;
        Zero : ReturnType;
        with function Func (P1 : Type1;
                            P2 : Type2;
                            J : IndexRange) return ReturnType;
        function Lemma_Sum_Odd_Even 

end SumGen;