<template>
  <div class="box">
    <q-card class="card_post">
      <q-tabs
        v-model="tab"
        class="my-tab"
        active-color="secondary"
        indicator-color="secondary"
        align="justify"
        narrow-indicator
      >
        <q-tab
          name="multimedia"
          label="Imagem/Vídeo"
          @click="showErrors = false"
        />
        <!--
        <q-tab
          name="criarEquipa"
          label="Criar Grupo"
          @click="showErrors = false"
        />-->
      </q-tabs>

      <q-separator />

      <q-tab-panels v-model="tab" animated>
        <!--Imagem/Video-->
        <q-tab-panel name="multimedia">
          <div class="row">
            <div class="col-md-5 col-xs-12 coluna_imagem">
              <q-file
                outlined
                v-model="m_selectedImage"
                class="upload_file"
                label="Adicionar Ficheiro"
                label-color="secondary"
                input-style="color:white"
              >
                <template v-slot:prepend>
                  <q-icon name="attach_file" color="secondary" />
                  <q-icon
                    v-if="m_selectedImage != null"
                    name="cancel"
                    @click="
                      m_selectedImage = null;
                      imageUrl = '';
                    "
                    class="cursor-pointer"
                    color="secondary"
                  ></q-icon>
                </template>
              </q-file>
              <q-item class="image_preview">
                <video v-if="isVideo(imageUrl)" controls class="the_image">
                  <source :src="imageUrl" type="video/mp4" />
                  Your browser does not support HTML video.
                </video>
                <q-img
                  v-else
                  :src="imageUrl"
                  class="the_image"
                  spinner-color="secondary"
                />
                <q-circular-progress
                  v-if="m_selectedImage != null && progress != 100"
                  show-value
                  font-size="15px"
                  :value="progress"
                  size="150px"
                  :thickness="0.22"
                  color="secondary"
                  track-color="black"
                  class="loading_bar"
                >
                  {{ progress }}%
                </q-circular-progress>
              </q-item>
            </div>
            <div class="col-md-7 col-xs-12 coluna_filtro">
              <q-select
                class="select_stuff"
                outlined
                use-chips
                v-model="m_selectedGame"
                :options="gameOptions"
                :dense="dense"
                :options-dense="denseOpts"
                label="Selecionar Jogo"
                label-color="secondary"
              >
                <template v-slot:prepend>
                  <q-icon name="sports_esports" color="secondary" />
                </template>
              </q-select>
              <span
                v-if="showErrors && m_selectedGame == null"
                class="error-msg"
              >
                *Campo obrigatório
              </span>

              <div class="row">
                <div class="col-12 coluna_filtro">
                  <q-select
                    outlined
                    multiple
                    use-chips
                    class="select_stuff"
                    v-model="m_selectedTags"
                    :options="tagOptions"
                    :dense="dense"
                    :options-dense="denseOpts"
                    label="Adicionar TAG"
                    label-color="secondary"
                  >
                    <template v-slot:prepend>
                      <q-icon name="local_offer" color="secondary" />
                    </template>
                  </q-select>
                </div>
              </div>

              <div class="row">
                <div class="col-12 coluna_filtro">
                  <q-input
                    class="select_stuff"
                    outlined
                    v-model="m_descricao"
                    :dense="dense"
                    :input-style="{ color: 'white' }"
                    label="Descrição"
                    label-color="secondary"
                  >
                    <template v-slot:prepend>
                      <q-icon name="description" color="secondary" />
                      <q-icon
                        v-if="m_descricao != ''"
                        name="cancel"
                        @click="m_descricao = ''"
                        class="cursor-pointer"
                        color="secondary"
                      ></q-icon>
                    </template>
                  </q-input>
                  <span
                    v-if="showErrors && m_descricao == ''"
                    class="error-msg"
                  >
                    *Campo obrigatório
                  </span>
                </div>
              </div>

              <div class="row buttons">
                <div class="coluna_filtro">
                  <q-btn class="btn_cancel" @click="cancel">Cancelar</q-btn>
                </div>
                <div class="coluna_filtro">
                  <q-btn class="btn_publicar" @click="publicar_multimedia"
                    >Publicar</q-btn
                  >
                </div>
              </div>
            </div>
          </div>
        </q-tab-panel>

        <!--Criar Equipa-->
        <q-tab-panel name="criarEquipa">
          <div class="row">
            <div class="col-md-4 col-xs-12 coluna_imagem">
              <q-input
                v-model="g_descricao"
                outlined
                clearable
                class="input_descricao"
                label="Descrição"
                label-color="secondary"
                :input-style="{ color: 'white' }"
                type="textarea"
              >
                <template v-slot:prepend>
                  <q-icon name="description" color="secondary" />
                  <q-icon
                    v-if="g_descricao != ''"
                    name="cancel"
                    @click="g_descricao = ''"
                    class="cursor-pointer"
                    color="secondary"
                  ></q-icon>
                </template>
              </q-input>
            </div>
            <div class="col-md-8 col-xs-12 coluna_filtro">
              <div class="row primeira_row">
                <div class="different_2">
                  <q-select
                    class="select_stuff"
                    outlined
                    use-chips
                    v-model="g_selectedGame"
                    :options="gameOptions"
                    :dense="dense"
                    :options-dense="denseOpts"
                    label="Jogo"
                    label-color="secondary"
                  >
                    <template v-slot:prepend>
                      <q-icon name="sports_esports" color="secondary" />
                    </template>
                  </q-select>
                  <span
                    v-if="showErrors && g_selectedGame == null"
                    class="error-msg"
                  >
                    *Campo obrigatório
                  </span>
                </div>

                <div class="different_2">
                  <q-select
                    class="select_stuff"
                    outlined
                    use-chips
                    v-model="g_selectedPlatform"
                    :options="g_platformOptions"
                    :dense="dense"
                    :options-dense="denseOpts"
                    label="Plataforma"
                    label-color="secondary"
                  >
                    <template v-slot:prepend>
                      <q-icon name="videogame_asset" color="secondary" />
                    </template>
                  </q-select>
                  <span
                    v-if="showErrors && g_selectedPlatform == null"
                    class="error-msg"
                  >
                    *Campo obrigatório
                  </span>
                </div>
              </div>

              <div class="row">
                <div class="col-12 coluna_filtro">
                  <q-input
                    class="select_stuff nome_select"
                    outlined
                    v-model="g_nome"
                    :dense="dense"
                    :input-style="{ color: 'white' }"
                    label="Nome da Equipa"
                    label-color="secondary"
                  >
                    <template v-slot:prepend>
                      <q-icon name="badge" color="secondary" />
                      <q-icon
                        v-if="g_nome != ''"
                        name="cancel"
                        @click="g_nome = ''"
                        class="cursor-pointer"
                        color="secondary"
                      ></q-icon>
                    </template>
                  </q-input>
                </div>
                <span v-if="showErrors && g_nome == ''" class="error-msg">
                  *Campo obrigatório
                </span>
              </div>
            </div>
          </div>

          <div class="row segunda_row">
            <div class="coluna_filtro different">
              <q-select
                class="select_stuff"
                outlined
                use-chips
                v-model="g_idioma"
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
            </div>
            <div class="coluna_filtro different">
              <q-select
                class="select_stuff"
                outlined
                use-chips
                v-model="g_modo"
                :options="modosOptions"
                :dense="dense"
                :options-dense="denseOpts"
                label="Modo"
                label-color="secondary"
              >
                <template v-slot:prepend>
                  <q-icon name="sports_kabaddi" color="secondary"></q-icon>
                </template>
              </q-select>
            </div>

            <div class="coluna_filtro different">
              <q-input
                class="select_stuff"
                outlined
                v-model="g_pessoas"
                :dense="dense"
                :input-style="{ color: 'white' }"
                label="Nº Pessoas"
                label-color="secondary"
                type="number"
              >
                <template v-slot:prepend>
                  <q-icon name="groups" color="secondary"></q-icon>
                  <q-icon
                    v-if="g_pessoas != null"
                    name="cancel"
                    @click="g_pessoas = null"
                    class="cursor-pointer"
                    color="secondary"
                  ></q-icon>
                </template>
              </q-input>
              <span v-if="showErrors && g_pessoas == null" class="error-msg">
                *Campo obrigatório
              </span>
            </div>
          </div>

          <div class="row buttons">
            <div class="coluna_filtro">
              <q-btn class="btn_cancel" @click="cancel">Cancelar</q-btn>
            </div>
            <div class="coluna_filtro">
              <q-btn class="btn_publicar" @click="publicar_grupo"
                >Criar Grupo
                <q-dialog v-model="showDialog" persistent>
                  <q-card class="bg-dark">
                    <q-card-section class="row items-center">
                      <q-avatar
                        icon="warning"
                        color="primary"
                        text-color="white"
                      />
                      <span class="q-ml-sm text-white">
                        Criar um grupo implica sair do seu grupo atual. Pretende
                        continuar?
                      </span>
                    </q-card-section>

                    <q-card-actions align="right">
                      <q-btn
                        outline
                        color="secondary"
                        label="Cancelar"
                        @click="cancelGroup"
                        v-close-popup
                      />
                      <q-btn
                        outline
                        color="secondary"
                        label="Confirmar"
                        @click="confirmGroup"
                        v-close-popup
                      />
                    </q-card-actions>
                  </q-card>
                </q-dialog>
              </q-btn>
            </div>
          </div>
        </q-tab-panel>
      </q-tab-panels>
    </q-card>
  </div>
</template>

<script>
import { ref } from "@vue/reactivity";
import { computed, onMounted, onUpdated } from "@vue/runtime-core";
import axios from "axios";
import URL from "../url.js";
import { useQuasar } from "quasar";
export default {
  setup() {
    const q = useQuasar();
    const progress = ref(0);

    //dados obtidos da base de dados
    const games = ref(null);
    const gameOptions = ref([]);
    const tagOptions = ref([]);
    const game_tags_data = ref([]);

    onMounted(async () => {
      //obter jogos do user(era melhor se passassemos info da página principal para esta, para não estarmos a fazer sempre gets)
      const user_jogos = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getListaJogosSeguir/" + localStorage.id,
      });

      const user_jogos_data = await user_jogos.data;
      games.value = user_jogos_data;
      user_jogos_data.forEach((g) => gameOptions.value.push(g.nome));

      //obter tags possíveis
      const games_tags = await axios({
        method: "get",
        url: URL.URL + "/posts/getTags",
      });

      game_tags_data.value = await games_tags.data;
      game_tags_data.value.forEach((t) => tagOptions.value.push("#" + t.tag));
    });

    return {
      tab: ref("multimedia"),
      dense: ref(false),
      denseOpts: ref(false),

      //media
      game_tags_data,
      games,
      m_selectedGame: ref(null),
      gameOptions,
      m_selectedTags: ref([]),
      tagOptions,
      m_descricao: ref(""),
      m_selectedImage: ref(null),
      imageUrl: ref(""),
      CLOUDINARY_URL:
        "https://api.cloudinary.com/v1_1/gamehubmultimedia/upload",
      CLOUDINARY_UPLOAD_PRESET: "xpjmvfcb",

      //grupo
      g_selectedGame: ref(null),

      g_selectedPlatform: ref(null),
      g_platformOptions: ref([]),

      g_idioma: ref(null),
      idiomasOptions: ["Português", "Inglês", "Alemão", "Espanhol"], //podia ter mais

      g_modo: ref(null),
      modosOptions: ["Competitivo", "Casual"], //podia ter mais?

      g_pessoas: ref(null),

      g_nome: ref(""),
      g_descricao: ref(""),
      progress,
      showErrors: ref(false),
      q,
      showDialog: ref(false),
    };
  },
  methods: {
    async publicar_multimedia() {
      if (this.m_selectedGame != null && this.m_descricao != "") {
        const tags_id = ref([]);

        this.game_tags_data.forEach((t) => {
          const tag = "#" + t.tag;
          if (this.m_selectedTags.includes(tag)) {
            tags_id.value.push(t.id);
          }
        });

        const res = await axios({
          method: "post",
          url: URL.URL + "/posts/createPostMedia/" + localStorage.id,
          data: {
            jogo: this.m_selectedGame,
            descricao: this.m_descricao,
            tags: tags_id.value,
            multimedia: this.imageUrl,
          },
        });

        const res_data = await res.data;

        this.q.notify({
          progress: true,
          message: "Publicação criada com sucesso!",
          color: "green",
          position: "bottom-right",
          actions: [
            {
              label: "Remover Publicação",
              color: "yellow",
              handler: async () => {
                await axios({
                  method: "post",
                  url: URL.URL + "/posts/deletePost/" + res_data,
                  params: {
                    tipo_post: 0,
                  },
                });
                this.q.notify({
                  progress: true,
                  message: "Publicação removida com sucesso!",
                  color: "green",
                  position: "bottom-right",
                });
              },
            },
          ],
        });

        this.$emit("setSelectedGame", this.m_selectedGame);
      } else {
        this.showErrors = true;
        this.q.notify({
          progress: true,
          message: "Por favor preencha os campos requeridos.",
          color: "red",
          position: "bottom-right",
        });
      }
    },

    cancel() {
      this.$router.push("/main");
    },

    async publicar_grupo() {
      if (
        this.g_selectedGame != null &&
        this.g_pessoas != null &&
        this.g_selectedPlatform != null &&
        this.g_nome != ""
      ) {
        const inGrupo = await axios({
          method: "get",
          url: URL.URL + "/utilizador/getGrupoID/" + localStorage.id,
        });

        const data_inGrupo = await inGrupo.data;

        if (data_inGrupo === -1) {
          const grupoid = await axios({
            method: "post",
            url: URL.URL + "/posts/createPostGrupo/" + localStorage.id,
            data: {
              jogo: this.g_selectedGame,
              descricao: this.g_descricao,
              idioma: this.g_idioma,
              modoJogo: this.g_modo,
              participantes: this.g_pessoas,
              nomeEquipa: this.g_nome,
              plataforma: this.g_selectedPlatform,
            },
          });
          this.$emit("joinedGroup");
          const data_grupoid = await grupoid.data;
          this.q.notify({
            progress: true,
            message: "Grupo criado com sucesso!",
            color: "green",
            position: "bottom-right",
            actions: [
              {
                label: "Remover publicação de Grupo",
                color: "yellow",
                handler: async () => {
                  await axios({
                    method: "post",
                    url: URL.URL + "/posts/deletePost/" + data_grupoid,
                    params: {
                      tipo_post: 1,
                    },
                  });
                  this.q.notify({
                    progress: true,
                    message: "Publicação de grupo removida com sucesso!",
                    color: "green",
                    position: "bottom-right",
                  });
                  this.$emit("joinedGroup");
                },
              },
            ],
          });
        } else {
          this.showDialog = true;
        }
        /* this.$router.push("/main"); */
      } else {
        this.showErrors = true;
        this.q.notify({
          progress: true,
          message: "Por favor preencha os campos requeridos.",
          color: "red",
          position: "bottom-right",
        });
      }
    },

    cancelGroup() {
      this.q.notify({
        progress: true,
        message: "Publicação de grupo cancelada!",
        color: "red",
        position: "bottom-right",
      });
    },

    async confirmGroup() {
      const grupoid = await axios({
        method: "post",
        url: URL.URL + "/posts/createPostGrupo/" + localStorage.id,
        data: {
          jogo: this.g_selectedGame,
          descricao: this.g_descricao,
          idioma: this.g_idioma,
          modoJogo: this.g_modo,
          participantes: this.g_pessoas,
          nomeEquipa: this.g_nome,
          plataforma: this.g_selectedPlatform,
        },
      });
      this.$emit("joinedGroup");
      const data_grupoid = await grupoid.data;
      this.q.notify({
        progress: true,
        message: "Grupo criado com sucesso!",
        color: "green",
        position: "bottom-right",
        actions: [
          {
            label: "Remover publicação de Grupo",
            color: "yellow",
            handler: async () => {
              await axios({
                method: "post",
                url: URL.URL + "/posts/deletePost/" + data_grupoid,
                params: {
                  tipo_post: 1,
                },
              });
              this.q.notify({
                progress: true,
                message: "Publicação de grupo removida com sucesso!",
                color: "green",
                position: "bottom-right",
              });
              this.$emit("joinedGroup");
            },
          },
        ],
      });
    },

    isVideo(multimedia) {
      const last = multimedia.split(".").pop();

      if (last == "mp4" || last == "mp3") return true;
      else return false;
    },
  },

  watch: {
    m_selectedImage: async function () {
      if (this.m_selectedImage != null) {
        var formData = new FormData();
        formData.append("file", this.m_selectedImage);
        formData.append("upload_preset", this.CLOUDINARY_UPLOAD_PRESET);

        var g = await axios({
          url: this.CLOUDINARY_URL,
          method: "POST",
          headers: {
            "Content-Type": "application/x-www-form-urlencoded",
          },
          data: formData,
          onUploadProgress: function (progressEvent) {
            this.progress = Math.round(
              (progressEvent.loaded * 100.0) / progressEvent.total
            );
          }.bind(this),
        });

        var g_data = await g.data;
        this.imageUrl = g_data.secure_url;
      }
    },

    g_selectedGame: function () {
      if (this.g_selectedGame != null) {
        const jogo = this.games.filter((g) => g.nome == this.g_selectedGame);
        jogo[0].plataformas.forEach((p) =>
          this.g_platformOptions.push(p.plataforma)
        );
      } else {
        this.g_selectedPlatform = null;
        this.g_platformOptions = [];
      }
    },
  },
};
</script>

<style scoped>
.card_post {
  background: rgb(0, 0, 0);
  color: rgb(110, 110, 110);
  width: 90%;
  margin: 5% auto;
  box-shadow: 0px 0px 20px 1px black;
  border-radius: 10px;
}

.coluna_filtro {
  margin-top: 20px;
}

.coluna_imagem {
  margin-top: 20px;
}

.buttons {
  margin-top: 10px;
  margin-bottom: 20px;
  display: flex;
  justify-content: space-between;
}

.primeira_row {
  justify-content: space-between;
}

.segunda_row {
  justify-content: space-between;
}

.different {
  width: 32%;
}

.different_2 {
  width: 48%;
}

.imagem_equipa {
  background: #1d1d1d;
  margin: 10px auto;
}

.q-tab-panels {
  /*height: 100%;*/
  background: #1d1d1d;
}

.btn_cancel {
  background: red;
  color: white;
}

.btn_cancel:hover {
  transform: scale(1.1);
}

.btn_convidar_amigos {
  background: rgb(0, 211, 70);
  color: white;
}

.btn_convidar_amigos:hover {
  transform: scale(1.1);
}

.btn_publicar {
  background: #005cc5;
  color: white;
}

.btn_publicar:hover {
  transform: scale(1.1);
}

.select_stuff {
  outline: none;
  border: none;
  border-radius: 5pt;
  box-shadow: 0 0 0 2px #ffd208;
}

.input_descricao {
  outline: none;
  border: none;
  border-radius: 5pt;
  box-shadow: 0 0 0 2px #ffd208;
  margin-right: 20px;
}

.image_preview {
  margin-left: 10px;
  margin-right: 20px;
  margin-top: 10px;
  background: #222222;
  border-radius: 10px;
}

.the_image {
  width: 100%;
  height: 200px;
  border-radius: 10px;
}

.upload_file {
  margin-left: 10px;
  margin-right: 20px;
  outline: none;
  border: none;
  border-radius: 5pt;
  box-shadow: 0 0 0 2px #ffd208;
}

.loading_bar {
  margin: auto;
  margin-right: 43%;
}

.nome_select {
  margin-top: 2%;
}

.error-msg {
  color: #ffd208;
  font-size: 12px;
  margin-top: 5px;
}
</style>
