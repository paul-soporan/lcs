<script setup lang="ts">
import { prove } from 'lcs_wasm';
import { computed } from 'vue';

const { knowledgeBase, goal, signature } = defineProps<{
  knowledgeBase: string[];
  goal: string;
  signature: {
    functions: Array<[string, string]>;
    predicates: Array<[string, string]>;
    constants: string[];
  };
}>();

const explainedResult = computed(() => {
  try {
    return prove(knowledgeBase, goal, signature);
  } catch (error) {
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    return (error as any).toString();
  }
});
</script>

<template>
  <div class="flex flex-row">
    <div class="flex-1" style="height: 75vh">
      <div v-if="typeof explainedResult.result === 'object'">
        <h2>Proof</h2>
        <div v-if="explainedResult.result.Ok">
          <p>Result: {{ explainedResult.result.Ok.result }}</p>
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
</template>
