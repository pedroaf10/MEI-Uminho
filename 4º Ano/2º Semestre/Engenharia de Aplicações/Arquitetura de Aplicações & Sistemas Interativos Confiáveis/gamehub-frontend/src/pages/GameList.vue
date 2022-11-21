<template>
  <div class="height">
    <div class="bg-primary search">
      <q-input
        color="secondary"
        filled
        label-color="secondary"
        v-model="text"
        input-style="color:white"
        label="Procurar Jogo"
      >
        <template v-slot:prepend>
          <q-icon name="search" color="secondary" />
        </template>
      </q-input>
    </div>

    <q-scroll-area
      :thumb-style="thumbStyle"
      :bar-style="barStyle"
      class="areaJogos"
    >
      <div v-if="!games" class="loading_games">
        <q-spinner
          color="primary"
          size="3em"
          :thickness="10"
        />
      <!--A carregar jogos...-->
      </div>
      <q-list v-else class="listaJogos">
        <div v-if="matchingGames.length" class="list">
          <q-item v-for="game in matchingGames" :key="game.game.id">
            <q-card
              v-if="game.selected"
              dark
              bordered
              class="bg-black-9 my-card zoom"
              @click="onClick(game.game)"
            >
              <div class="text-h6">{{ game.game.nome }}</div>
              <q-img
                :src="game.game.bannerLink"
                class="background"
                spinner-color="secondary"
              />
            </q-card>
            <q-card
              v-else
              dark
              bordered
              class="bg-grey-9 my-card"
              @click="onClick(game.game)"
            >
              <div class="text-h6" style="font-weight: bold">
                {{ game.game.nome }}
              </div>
              <q-img
                :src="game.game.bannerLink"
                class="background"
                spinner-color="secondary"
              />
            </q-card>
          </q-item>
        </div>
        <div v-else class="notFound text-white text-bold">Nenhum item corresponde à pesquisa.</div>
      </q-list>
    </q-scroll-area>

    <div class="zona_buttons">
      <q-btn class="btn_cancel text-bold" label="Cancelar" @click="cancel"></q-btn>

      <q-btn
        class="btn_addGames text-black text-bold"
        v-if="!selectedGames.length && matchingGames.length"
        color="secondary"
        label="Adicionar Jogos"
      >
        <q-popup-proxy>
          <q-banner class="bg-red-9">
            <template v-slot:avatar>
              <q-icon name="error" color="primary" />
            </template>
            Não adicionou nenhum jogo!
          </q-banner>
        </q-popup-proxy>
      </q-btn>

      <q-btn
        class="btn_addGames"
        glossy
        v-if="selectedGames.length && matchingGames.length"
        color="secondary"
        label="Adicionar Jogos"
        @click="addGames"
      >
        <q-popup-proxy>
          <q-banner class="bg-green-9">
            <template v-slot:avatar>
              <q-icon name="done" color="primary" />
            </template>
            Adicionados os jogos:
            <span v-for="(game, index) in selectedGames" :key="game">
              {{ game.game.nome }}
              <span v-if="index != selectedGames.length - 1">, </span>
            </span>
          </q-banner>
        </q-popup-proxy>
      </q-btn>
    </div>
  </div>
</template>

<script>
import { ref } from "@vue/reactivity";
import { computed, onMounted } from "@vue/runtime-core";
import axios from "axios";
import URL from "../url.js";
export default {
  name: "GameList",
  props: {
    myGames: {
      type: Object,
    },
  },
  setup() {
    const games = ref(null);
    const selected = ref([]);

    onMounted(async () => {
      const result_getJogos = await axios({
        method: "get",
        url: URL.URL + "/utilizador/jogosporseguir/" + localStorage.id,
      });
      const result_data_getJogos = await result_getJogos.data;
      games.value = result_data_getJogos;
      games.value.forEach((game) =>
        selected.value.push({ game: game, selected: false })
      );
    });

    const onClick = (game) => {
      const objIndex = selected.value.findIndex((g) => g.game.id === game.id);
      selected.value[objIndex].selected = !selected.value[objIndex].selected;
    };

    const selectedGames = computed(() => {
      return selected.value.filter((game) => game.selected);
    });

    const text = ref("");
    const matchingGames = computed(() => {
      return selected.value.filter((game) =>
        game.game.nome.toLowerCase().includes(text.value.toLowerCase())
      );
    });

    return {
      thumbStyle: {
        right: "4px",
        borderRadius: "5px",
        backgroundColor: "#ffd208",
        width: "4px",
        opacity: 0.75,
      },
      barStyle: {
        right: "2px",
        borderRadius: "9px",
        width: "2px",
        opacity: 0.2,
      },
      games,
      onClick,
      selectedGames,
      text,
      matchingGames,
    };
  },
  methods: {
    addGames() {
      //os props veem sempre undefined
      const result = [];

      const gamesToAdd = this.selectedGames.filter((g) => g.selected === true);
      gamesToAdd.forEach((g) => result.push(g.game));
      const data = gamesToAdd.map(function (obj) {
        return obj.game.id;
      });

      axios({
        method: "post",
        url: URL.URL + "/utilizador/addJogoSeguir/" + localStorage.id,
        data: {
          jogos: data,
        },
      });

      this.$emit("gamesToAdd", result);
      setTimeout(() => {
        this.$router.push("/main");
      }, 1000);
    },
    cancel() {
      this.$router.push("/main");
    },
  },
};
</script>

<style scoped>
.my-card {
  cursor: pointer;
  transition: transform 0.1s;
  width: 90%;
  margin: 5px auto;
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding-left: 20px;
}
.my-card:hover {
  transform: scale(1.05);
}

.bg-grey-9.my-card > .background {
  filter: grayscale(100%);
}

.bg-grey-9.my-card:hover > .background {
  filter: none;
}

.notFound {
  font-size: 30px;
  text-align: center;
  margin: auto;
  width: 90%;
  margin-top: 20px;
}

.background {
  width: 60%;
  -webkit-clip-path: polygon(0 0, 100% 0, 100% 100%, 7% 100%);
  clip-path: polygon(0 0, 100% 0, 100% 100%, 7% 100%);
}

.height {
  height: 89vh;
  overflow: auto;
}

.search {
  position: -webkit-sticky;
  position: sticky;
  top: 0;
  z-index: 2;
}

.areaJogos {
  width: 100%;
  height: 81%;
}

.listaJogos {
  height: 100%;
}

.zona_buttons {
  display: flex;
  margin-top: 15px;
  justify-content: space-between;
  padding-left: 6%;
  padding-right: 6%;
}

.btn_addGames {
  position: relative;
}

.btn_addGames:hover {
  transform: scale(1.05);
}

.btn_cancel {
  background: red;
  color: white;
}

.btn_cancel:hover {
  transform: scale(1.05);
}

.loading_games{
  height: 200px;
  width: 100%;
}

</style>
