<script setup lang="ts">
import DataTable from 'primevue/datatable';
import Column, { type ColumnState } from 'primevue/column';
import InputText from 'primevue/inputtext';
import { computed, ref } from 'vue';
import ListItemForm from '@/components/ListItemForm.vue';
import DetailedProof from '@/components/DetailedProof.vue';
import FloatLabel from 'primevue/floatlabel';
import Button from 'primevue/button';

type BodycellPassThroughMethodOptions = {
  state: ColumnState;
};

const knowledgeBaseFormulas = ref<Array<{ formula: string }>>([]);
const knowledgeBase = computed(() => knowledgeBaseFormulas.value.map(({ formula }) => formula));

const goal = ref('');

const functions = ref('f/2, g/1');
const predicates = ref('P/2, Q/3');
const constants = ref('a, b, c');

const COMMA_REGEX = /\s*,\s*/;

const signature = computed(() => ({
  functions: functions.value.split(COMMA_REGEX).map((f) => {
    const [name, arity] = f.split('/');
    return [name, Number(arity)];
  }),
  predicates: predicates.value.split(COMMA_REGEX).map((p) => {
    const [name, arity] = p.split('/');
    return [name, Number(arity)];
  }),
  constants: constants.value.split(COMMA_REGEX).map((c) => c),
}));
</script>

<template>
  <main class="flex flex-column p-2">
    <div class="flex flex-row">
      <div class="flex-1">
        <DataTable
          :value="knowledgeBaseFormulas"
          edit-mode="cell"
          @cell-edit-complete="(event) => (event.data.formula = event.newValue)"
          :pt="{
            table: { style: 'min-width: 50rem' },
            column: {
              bodycell: ({ state }: BodycellPassThroughMethodOptions) => ({
                class: [{ '!py-0': state['d_editing'] }],
              }),
            },
          }"
        >
          <Column field="formula" header="Knowledge Base">
            <template #editor="{ data, field }">
              <InputText v-model="data[field]" autofocus fluid />
            </template>
          </Column>
          <Column>
            <template #body="{ index }">
              <Button
                icon="pi pi-times"
                class="p-button-danger"
                outlined
                rounded
                size="small"
                @click="knowledgeBaseFormulas.splice(index, 1)"
              />
            </template>
          </Column>
          <template #footer>
            <ListItemForm @submit="(formula) => knowledgeBaseFormulas.push({ formula })" />
          </template>
        </DataTable>
        <div class="flex">
          <h3>Goal:</h3>
          <InputText v-model="goal" placeholder="Write a goal here" class="ml-3" />
          <h4 class="ml-8">If something goes wrong, just refresh.</h4>
        </div>
      </div>
      <div class="flex-1 ml-8">
        <span class="flex">
          <h1>Signature</h1>
          <span class="mt-4 ml-4"
            >Common math signature is already included (common operations + (in)equality
            predicates).<br />Functions and predicates with arity 2 implicitly support infix
            notation (same precedence, left associative).</span
          >
        </span>
        <div class="flex flex-row mt-3">
          <FloatLabel variant="on">
            <InputText v-model="functions" id="functions" />
            <label for="functions">Functions</label>
          </FloatLabel>
          <FloatLabel variant="on">
            <InputText v-model="predicates" id="predicates" />
            <label for="predicates">Predicates</label>
          </FloatLabel>
          <FloatLabel variant="on">
            <InputText v-model="constants" id="constants" />
            <label for="constants">Constants</label>
          </FloatLabel>
        </div>
      </div>
    </div>
    <DetailedProof :knowledge-base :goal :signature="signature as any" />
  </main>
</template>
