<script setup lang="ts">
import InputText from 'primevue/inputtext';
import Button from 'primevue/button';
import { ref } from 'vue';

const emit = defineEmits<{
  submit: [field: string];
}>();

const isShown = ref(false);

const field = ref('');

function onSubmit(event: Event) {
  emit('submit', field.value);

  field.value = '';

  (event.target as HTMLFormElement).reset();
}
</script>

<template>
  <form v-if="isShown" @submit.prevent="onSubmit" @reset="isShown = false" class="flex gap-5">
    <div class="flex-1 flex gap-3">
      <InputText v-model="field" type="text" placeholder="Formula" class="w-3" />
    </div>
    <span class="p-buttonset">
      <Button type="submit" icon="pi pi-check" outlined />
      <Button type="reset" icon="pi pi-times" severity="danger" outlined />
    </span>
  </form>
  <div v-else class="flex">
    <Button @click="isShown = true" label="Add formula" icon="pi pi-plus" outlined />
    <h4 class="ml-8">Hint: Cells are editable.</h4>
  </div>
</template>
