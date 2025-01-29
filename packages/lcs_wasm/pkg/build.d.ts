/* tslint:disable */
/* eslint-disable */
export function prove(knowledge_base: string[], goal: string, simple_signature: SimpleSignature): ExplainedResult;
export interface ExplainedResult<T> {
    result: { Ok: T } | { Err: string };
    explanation: string;
}

export interface DetailedProof {
    result: string;
    description: string;
}

export interface SimpleSignature {
    functions: [string, number][];
    predicates: [string, number][];
    constants: string[];
}

