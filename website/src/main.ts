import PrimeVue from 'primevue/config';
import { createApp } from 'vue';
import { createPinia } from 'pinia';
import Aura from '@primevue/themes/aura';

import 'primeflex/primeflex.css';
import 'primeicons/primeicons.css';

import 'primeflex/themes/primeone-dark.css';

import App from './App.vue';
import router from './router';

const app = createApp(App);

app.use(PrimeVue, {
  theme: {
    preset: Aura,
  },
});

app.use(createPinia());
app.use(router);

app.mount('#app');
