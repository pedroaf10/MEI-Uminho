<template>
  <div>
    <q-card class="card_joinTeam">
      <q-card-section horizontal class="filtros">
        <q-select
          class="select_stuff"
          outlined
          use-chips
          v-model="selectedGame"
          :options="gameOptions"
          :dense="dense"
          :options-dense="denseOpts"
          label="Jogo"
          label-color="secondary"
        >
          <template v-slot:prepend>
            <q-icon name="sports_esports" color="secondary"></q-icon>
          </template>
        </q-select>

        <q-select
          class="select_stuff"
          outlined
          use-chips
          v-model="selectedPlatform"
          :options="platformOptions"
          :dense="dense"
          :options-dense="denseOpts"
          label="Plataforma"
          label-color="secondary"
        >
          <template v-slot:prepend>
            <q-icon name="videogame_asset" color="secondary"></q-icon>
          </template>
          <q-tooltip
            v-if="selectedGame == null"
            class="bg-accent"
            :offset="[10, 10]"
          >
            <strong
              >Para selecionar uma plataforma, tem de primeiro selecionar um
              jogo</strong
            >
          </q-tooltip>
        </q-select>

        <q-select
          class="select_stuff"
          outlined
          use-chips
          v-model="selectedModo"
          :options="modoOptions"
          :dense="dense"
          :options-dense="denseOpts"
          label="Modo de Jogo"
          label-color="secondary"
        >
          <template v-slot:prepend>
            <q-icon name="sports_kabaddi" color="secondary"></q-icon>
          </template>
        </q-select>

        <q-select
          class="select_stuff"
          outlined
          use-chips
          v-model="selectedIdioma"
          :options="idiomasOptions"
          :dense="dense"
          :options-dense="denseOpts"
          label="Idioma"
          label-color="secondary"
        >
          <template v-slot:prepend>
            <q-icon name="public" color="secondary"></q-icon>
          </template>
        </q-select>
      </q-card-section>

      <q-card-section class="filtros">
        <q-input
          class="input_stuff"
          outlined
          v-model="selectedName"
          :dense="dense"
          :input-style="{ color: 'white' }"
          label="Procurar Nome do Grupo"
          label-color="secondary"
        >
          <template v-slot:prepend>
            <q-icon name="search" color="secondary" />
            <q-icon
              v-if="selectedName != ''"
              name="cancel"
              @click="selectedName = ''"
              class="cursor-pointer"
              color="secondary"
            ></q-icon>
          </template>
        </q-input>
      </q-card-section>

      <q-separator />

      <q-scroll-area
        :thumb-style="thumbStyle"
        :bar-style="barStyle"
        class="areaEquipas"
      >
        <q-list>
          <q-item v-for="g in matchingGrupos" :key="g.id">
            <q-card class="cartao_equipa">
              <img :src="getGameBanner(g.jogo)" class="equipa_image" />
              <p class="team_name">{{ g.nomeEquipa }}</p>
              <q-item>
                <q-item-section class="caixa">
                  <q-item-section>
                    <q-item-label class="titulo">Criador</q-item-label>
                    <q-item-label caption class="descricao">{{
                      g.gamer.nome
                    }}</q-item-label>
                  </q-item-section>
                </q-item-section>

                <q-item-section class="caixa">
                  <q-item-section>
                    <q-item-label class="titulo">Descrição</q-item-label>
                    <q-item-label
                      v-if="g.descricao"
                      caption
                      class="descricao"
                      >{{ g.descricao }}</q-item-label
                    >
                    <q-item-label v-else caption class="descricao">
                      -
                    </q-item-label>
                  </q-item-section>
                </q-item-section>

                <q-item-section class="caixa">
                  <q-item-label class="titulo">Jogabilidade</q-item-label>
                  <q-item-label caption class="descricao"
                    >Plataforma: {{ g.plataforma }}</q-item-label
                  >
                  <q-item-label v-if="g.modoJogo" caption class="descricao"
                    >Modo de Jogo: {{ g.modoJogo }}</q-item-label
                  >
                  <q-item-label v-else caption class="descricao"
                    >Modo de Jogo: Não especificado</q-item-label
                  >
                </q-item-section>

                <q-item-section class="caixa">
                  <q-item-label class="titulo">Comunicação</q-item-label>
                  <q-item-label v-if="g.idioma" caption class="descricao"
                    >Idioma: {{ g.idioma }}</q-item-label
                  >
                  <q-item-label v-else caption class="descricao"
                    >Idioma: Não especificado</q-item-label
                  >
                </q-item-section>

                <q-item-section class="caixa">
                  <q-item-label
                    class="descricao"
                    v-if="grupo_and_elements != null"
                    >Membros: {{ getNumberUsersAlreadyInGroup(g.id) }} /
                    {{ g.participantes }}</q-item-label
                  >
                  <q-btn
                    class="btn_juntar q-mt-xs"
                    :disable="alreadyInThatGroup(g.id)"
                    @click="propmtJoinGroup(g.nomeEquipa, g.id)"
                    >Juntar</q-btn
                  >
                  <q-dialog v-model="showConfirmation" persistent>
                    <q-card class="bg-dark">
                      <q-card-section class="row items-center">
                        <q-avatar
                          icon="warning"
                          color="primary"
                          text-color="white"
                        />
                        <span class="q-ml-sm text-white"> {{ text }}</span>
                      </q-card-section>

                      <q-card-actions align="right">
                        <q-btn
                          outline
                          color="secondary"
                          label="Cancelar"
                          v-close-popup
                        />
                        <q-btn
                          outline
                          color="secondary"
                          label="Confirmar"
                          @click="joinGroup"
                          v-close-popup
                        />
                      </q-card-actions>
                    </q-card>
                  </q-dialog>
                </q-item-section>
              </q-item>
            </q-card>
          </q-item>
        </q-list>
        <div
          v-if="!matchingGrupos.length"
          class="text-white text-bold notFound"
        >
          Não existem grupos disponíveis para os jogos que segue.
        </div>
      </q-scroll-area>
    </q-card>

    <q-btn class="btn_cancel" @click="cancel">Cancelar</q-btn>
  </div>
</template>

<script>
import { ref } from "@vue/reactivity";
import { computed, onMounted } from "@vue/runtime-core";
import axios from "axios";
import URL from "../url.js";
import { useQuasar } from "quasar";
export default {
  setup(props, { emit }) {
    const q = useQuasar();
    //dados obtidos da base de dados
    const gameOptions = ref([]);
    const game_and_banner = ref([]);
    const groups = ref([]);
    const games = ref(null);
    const meu_grupo_id = ref(null);
    const grupo_and_elements = ref([1]);
    const showConfirmation = ref(false);

    onMounted(async () => {
      //obter jogos do user
      const user_jogos = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getListaJogosSeguir/" + localStorage.id,
      });

      const user_jogos_data = await user_jogos.data;
      games.value = user_jogos_data;
      user_jogos_data.forEach(
        (g) =>
          gameOptions.value.push(g.nome) &&
          game_and_banner.value.push({ nome: g.nome, bannerURL: g.bannerLink })
      );

      //obter grupos
      const all_groups = await axios({
        method: "get",
        url: URL.URL + "/posts/postsGrupo",
      });

      const all_groups_data = await all_groups.data;
      all_groups_data.forEach(async (g) => {
        if (gameOptions.value.includes(g.jogo)) {
          groups.value.push(g);
          const d = await axios({
            method: "get",
            url: URL.URL + "/utilizador/getGrupo/" + g.id,
          });

          const group_info = await d.data;
          grupo_and_elements.value.push({
            id: g.id,
            elementos: group_info.gamers.length,
          });
        }
      });

      //obter id do meu grupo
      const id = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getGrupoID/" + localStorage.id,
      });

      const id_data = await id.data;
      meu_grupo_id.value = id_data;
    });

    const selectedModo = ref(null);
    const selectedIdioma = ref(null);
    const selectedName = ref("");
    const selectedGame = ref(null);
    const selectedPlatform = ref(null);

    const matchingGrupos = computed(() => {
      const m = groups.value
        .filter(
          (g) =>
            g.modoJogo == null ||
            g.modoJogo.includes(selectedModo.value) ||
            selectedModo.value == null
        )
        .filter(
          (g) =>
            g.idioma == null ||
            g.idioma.includes(selectedIdioma.value) ||
            selectedIdioma.value == null
        )
        .filter(
          (g) =>
            g.jogo.includes(selectedGame.value) || selectedGame.value == null
        )
        .filter((g) => gameOptions.value.includes(g.jogo))
        .filter(
          (g) =>
            g.plataforma.includes(selectedPlatform.value) ||
            selectedPlatform.value == null
        )
        .filter((g) =>
          g.nomeEquipa.toLowerCase().includes(selectedName.value.toLowerCase())
        );

      return m.filter((g) => {
        const save = grupo_and_elements.value.filter((el) => el.id === g.id)[0];

        if (save) {
          return save.elementos != 0;
        }
      });
    });

    const text = ref("");
    const clickedGroup = ref("");
    const propmtJoinGroup = (groupname, id) => {
      if (meu_grupo_id.value != -1) {
        showConfirmation.value = true;
        clickedGroup.value = id;
        text.value =
          'Já está num grupo. Pretende juntar-se ao grupo "' +
          groupname +
          '" ?';
      } else {
        showConfirmation.value = true;
        clickedGroup.value = id;
        text.value = 'Pretende juntar-se ao grupo "' + groupname + '" ?';
      }
    };

    const joinGroup = async () => {
      const response = await axios({
        method: "post",
        url: URL.URL + "/utilizador/juntarGrupo/" + localStorage.id,
        params: {
          id_post_grupo: clickedGroup.value,
        },
      });
      const response_data = await response.data;

      if (response_data == true && meu_grupo_id.value != -1) {
        grupo_and_elements.value.forEach((g) => {
          if (g.id == meu_grupo_id.value) {
            g.elementos -= 1;
          }
        });
        grupo_and_elements.value.forEach((g) => {
          if (g.id == clickedGroup.value) {
            g.elementos += 1;
          }
        });
        emit("joinedGroup");
        meu_grupo_id.value = clickedGroup.value;
        q.notify({
          progress: true,
          message: "Juntou-se ao grupo com sucesso!",
          color: "green",
          position: "bottom-right",
          actions: [
            {
              label: "Sair do grupo",
              color: "yellow",
              handler: async () => {
                await axios({
                  method: "post",
                  url: URL.URL + "/utilizador/sairGrupo/" + localStorage.id,
                });
                emit("joinedGroup");
                grupo_and_elements.value.forEach((g) => {
                  if (g.id == clickedGroup.value) {
                    g.elementos -= 1;
                  }
                });
                meu_grupo_id.value = -1;
              },
            },
          ],
        });
      } else if (response_data == true) {
        grupo_and_elements.value.forEach((g) => {
          if (g.id == clickedGroup.value) {
            g.elementos += 1;
          }
        });
        emit("joinedGroup");

        meu_grupo_id.value = clickedGroup.value;
        q.notify({
          progress: true,
          message: "Juntou-se ao grupo com sucesso!",
          color: "green",
          position: "bottom-right",
          actions: [
            {
              label: "Sair do grupo",
              color: "yellow",
              handler: async () => {
                await axios({
                  method: "post",
                  url: URL.URL + "/utilizador/sairGrupo/" + localStorage.id,
                });
                emit("joinedGroup");
                grupo_and_elements.value.forEach((g) => {
                  if (g.id == clickedGroup.value) {
                    g.elementos -= 1;
                  }
                });
                meu_grupo_id.value = -1;
              },
            },
          ],
        });
      } else {
        q.notify({
          progress: true,
          message: "Grupo já está cheio!",
          color: "red",
          position: "bottom-right",
        });

        groups.value = groups.value.filter((g) => g.id !== clickedGroup.value);
      }
    };

    return {
      dense: ref(false),
      denseOpts: ref(false),
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
      q,
      grupo_and_elements,
      games,
      meu_grupo_id,
      matchingGrupos,
      groups,
      game_and_banner,
      getGameBanner(nome) {
        const game = this.game_and_banner.filter((g) => g.nome == nome);
        if (game.length > 0) {
          return game[0].bannerURL;
        }
      },

      selectedModo,
      modoOptions: ["Casual", "Competitivo"],

      selectedIdioma,
      idiomasOptions: ["Português", "Inglês", "Alemão", "Espanhol"],

      selectedGame,
      gameOptions,

      selectedPlatform,
      platformOptions: ref([]),

      selectedName,
      joinGroup,
      showConfirmation,
      text,
      propmtJoinGroup,
    };
  },
  methods: {
    alreadyInThatGroup(groupID) {
      return groupID === this.meu_grupo_id;
    },

    cancel() {
      this.$router.push("/main");
    },

    getNumberUsersAlreadyInGroup(groupID) {
      const res = this.grupo_and_elements.filter((g) => g.id == groupID)[0];
      if (res != null)
        return this.grupo_and_elements.filter((g) => g.id == groupID)[0]
          .elementos;
      return -1;
    },
  },
  watch: {
    selectedGame: function () {
      if (this.selectedGame != null) {
        const jogo = this.games.filter((g) => g.nome == this.selectedGame);
        jogo[0].plataformas.forEach((p) =>
          this.platformOptions.push(p.plataforma)
        );
      } else {
        this.selectedPlatform = null;
        this.platformOptions = [];
      }
    },
  },
};
</script>

<style scoped>
.card_joinTeam {
  background: #222222;
  color: rgb(110, 110, 110);
  width: 90%;
  margin: 4% auto;
  box-shadow: 0px 0px 20px 1px black;
  border-radius: 10px;
}

.select_stuff {
  width: 100%;
  margin-right: 20px;
  margin-left: 20px;
  margin-top: 20px;
  background: #000000;
  border: 2px solid #ffd208;
  border-radius: 10px;
  color: white;
}

.input_stuff {
  width: 100%;
  background: #000000;
  border: 2px solid #ffd208;
  border-radius: 10px;
}

.filtros {
  background: #000000;
  display: flex;
  flex-direction: row;
}

.areaEquipas {
  padding: 10px;
  height: 45vh;
  background: #222222;
}

.cartao_equipa {
  margin: auto;
  background: #1d1d1d;
  color: white;
  font-weight: bold;
  align-items: center;
}

.equipa_image {
  height: 100%;
}

.info_equipa_nome {
  background: red;
  width: 20px;
}

.info_equipa_membros {
  background: rgb(0, 184, 61);
  width: 10px;
}

.info_equipa_btn {
  background: rgb(38, 0, 255);
  justify-content: center;
}

.btn_juntar {
  background: #005cc5;
  color: white;
  width: 100px;
  font-weight: bold;
}

.btn_juntar:disabled {
  background: grey;
}

.btn_juntar:hover {
  transform: scale(1.1);
}

.btn_cancel {
  background: red;
  color: white;
  width: 100px;
  font-weight: bold;
  margin-left: 5%;
  margin-top: -2%;
}

.btn_cancel:hover {
  transform: scale(1.05);
}

.caixa {
  align-content: center;
  align-items: center;
  text-align: center;
  margin: 10px;
}

.team_name {
  font-size: 40px;
  font-weight: bold;
  position: absolute;
  top: 30%;
  left: 50%;
  transform: translate(-50%, -50%);
  text-shadow: 1px 1px 10px black;
}

.titulo {
  color: #ffffff;
}

.descricao {
  color: white;
  inline-size: 150px;
  overflow-wrap: break-word;
}

.notFound {
  font-size: 25px;
  text-align: center;
  margin: auto;
  width: 90%;
  margin-top: 20px;
}

@media only screen and (max-width: 1200px) {
  .filtros {
    flex-direction: column;
  }
  .select_stuff {
    margin-right: 0px;
    margin-left: 0px;
  }
}
</style>
