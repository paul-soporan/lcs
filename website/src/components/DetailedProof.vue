<script setup lang="ts">
import { prove, type DetailedProof, type ExplainedResult } from 'lcs_wasm';
import { ref } from 'vue';

const { knowledgeBase, goal, signature } = defineProps<{
  knowledgeBase: string[];
  goal: string;
  signature: {
    functions: Array<[string, string]>;
    predicates: Array<[string, string]>;
    constants: string[];
  };
}>();

type ProofResult = ExplainedResult<DetailedProof> | string;

function computeProof(): ProofResult {
  try {
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    return prove(knowledgeBase, goal, signature as any);
  } catch (error) {
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    return (error as any).toString();
  }
}

function updateProof() {
  explainedResult.value = computeProof();
}

defineExpose({ updateProof });

const explainedResult = ref<ProofResult | null>(null);
</script>

<template>
  <div>
    <div v-if="explainedResult !== null" class="flex flex-row">
      <div class="flex-1" style="height: 75vh">
        <div v-if="typeof explainedResult === 'object'">
          <h2>Proof</h2>
          <div v-if="'Ok' in explainedResult.result">
            <p>
              Result:
              <span>
                <span v-if="explainedResult.result.Ok.result === 'proven'" class="text-green-400"
                  >proven</span
                >
                <span
                  v-else-if="explainedResult.result.Ok.result === 'contradiction'"
                  class="text-red-400"
                  >contradiction</span
                >
                <span
                  v-else-if="explainedResult.result.Ok.result === 'unknown'"
                  class="text-blue-400"
                  >unknown</span
                >
              </span>
            </p>
            <div v-html="explainedResult.result.Ok.description" />
          </div>
          <div v-else>
            <div class="text-red-500">{{ explainedResult.result.Err }}</div>
          </div>
        </div>
        <div v-else>
          <div>
            An unexpected error has occured while generating the proof:
            <div class="text-red-500">{{ explainedResult }}</div>
          </div>
        </div>
      </div>
      <div class="flex-1 overflow-scroll" style="height: 75vh">
        <h2>Program Steps</h2>
        <div v-html="explainedResult.explanation" />
      </div>
    </div>
    <div v-else class="flex justify-content-center align-items-center h-30rem">
      <span class="border-1 border-round-2xl p-4 text-3xl"
        >Please press the "Prove" button to build a proof.</span
      >
    </div>
  </div>
</template>
