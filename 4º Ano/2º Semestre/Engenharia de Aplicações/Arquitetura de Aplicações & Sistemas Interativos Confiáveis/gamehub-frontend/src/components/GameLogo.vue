<template>
  <router-link
    @click="$emit('selectGame', nome)"
    :to="{ name: 'JogoSelecionado', params: { id: gameid } }"
  >
    <q-menu class="bg-accent" context-menu anchor="top right" self="top left">
      <q-list style="min-width: 100px">
        <q-item clickable v-close-popup @click="$emit('stopFollowing', gameid)">
          <q-item-section>Deixar de seguir</q-item-section>
        </q-item>
      </q-list>
    </q-menu>
    <img :src="link" class="button_game" />
    <q-tooltip
      anchor="center right"
      self="center left"
      class="bg-accent"
      :offset="[10, 10]"
    >
      <strong>{{ nome }}</strong>
    </q-tooltip>
  </router-link>
</template>

<script>
import { ref } from "vue";
export default {
  props: ["link", "nome", "gameid"],
  setup(props) {
    return {};
  },
};
</script>

<style scoped>
.button_game {
  width: 58px;
  height: 58px;
  object-fit: cover;
  object-position: 100% 0;
  border-radius: 50%;
  box-shadow: 2px 2px 2px 2px rgb(0, 0, 0);
}

.button_game:hover {
  border-radius: 40%;
  transform: scale(1.1);
}
.q-item:hover {
  background: red;
  color: white;
}
</style>
