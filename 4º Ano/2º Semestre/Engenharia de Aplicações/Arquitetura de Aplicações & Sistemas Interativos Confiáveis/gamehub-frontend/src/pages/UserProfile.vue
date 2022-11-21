<template>
  <div class="box">
    <q-scroll-area
      :thumb-style="thumbStyle"
      :bar-style="barStyle"
      class="areaPosts"
      ref="feedscroll"
    >
      <q-scroll-observer @scroll="updateSavedHeight" />
      <q-btn
        rounded
        icon="arrow_upward"
        label="Voltar ao Topo"
        class="btn_top"
        id="button_scrollTop"
        @click="scrollToTop()"
      />
      <q-card dark class="profile_card">
        <q-card-section v-if="utilizador" horizontal>
          <q-card-section class="left_zone">
            <q-avatar round size="100px">
              <q-img :src="user_avatar" class="imagem_avatar" />
              <q-badge
                floating
                :color="utilizador.estado == 'Online' ? 'green' : 'grey'"
                rounded
                :label="utilizador.estado"
              />
            </q-avatar>

            <q-btn
              class="reset_avatar"
              @click="reset_avatar"
              :disable="
                user_avatar ==
                'https://api.multiavatar.com/' + this.official_username + '.png'
              "
              >Reset Avatar</q-btn
            >

            <q-file
              use-chips
              outlined
              standout
              v-model="selected_image"
              class="upload_file"
              label="Escolher Avatar"
              label-color="white"
            >
              <template v-slot:prepend> </template>
            </q-file>

            <q-card-section>
              <q-item-section>
                <q-item-section>
                  <q-input
                    class="username"
                    color="secondary"
                    filled
                    label-color="secondary"
                    :input-style="{ color: 'white' }"
                    v-model="new_username"
                    :label="official_username"
                    maxlength="18"
                  >
                    <template v-slot:prepend>
                      <q-icon name="edit" color="secondary" />
                    </template>
                  </q-input>
                </q-item-section>
              </q-item-section>
            </q-card-section>

            <q-rating
              v-model="utilizador.classificacao"
              size="2em"
              max="5"
              :color="
                utilizador.classificacao > 4
                  ? 'green'
                  : utilizador.classificacao > 2
                  ? 'yellow'
                  : 'red'
              "
              readonly
            />

            <div
              style="display: flex; justify-content: center; margin-top: 5px"
            >
              <p style="font-weight: bold">Classificação:</p>
              <p
                :style="
                  'margin-left: 5px; font-weight: bold; color: ' +
                  (utilizador.classificacao > 4
                    ? 'green'
                    : utilizador.classificacao > 2
                    ? 'yellow'
                    : 'red')
                "
              >
                {{ utilizador.classificacao }}
              </p>
            </div>

            <div class="buttons row">
              <div class="col-xs-12">
                <q-btn
                  size="sm"
                  class="button_save"
                  @click="save"
                  :disable="!changes_made"
                  >Guardar</q-btn
                >
                <q-tooltip
                  v-if="!changes_made"
                  class="bg-accent"
                  :offset="[0, 0]"
                >
                  <strong>Não realizou nenhuma alteração</strong>
                </q-tooltip>
              </div>
            </div>
          </q-card-section>

          <q-separator vertical />

          <q-card-section class="right_zone">
            <q-card-section horizontal class="icon_e_titulo">
              <q-icon size="40px" color="secondary" name="emoji_events" />
              <p class="recompensa">Recompensas</p>
            </q-card-section>

            <q-scroll-area
              :thumb-style="thumbStyle"
              :bar-style="barStyle"
              class="area_recompensas"
            >
              <q-list v-if="utilizador.recompensas.length > 0">
                <q-card-section
                  v-for="recompensa in utilizador.recompensas"
                  :key="recompensa"
                  horizontal
                  class="card_recompensa"
                >
                  <q-avatar size="30px">
                    <q-img :src="recompensa.imageLink" />
                  </q-avatar>

                  <p class="nome_recompensa">{{ recompensa.nome }}</p>
                </q-card-section>
                <q-tooltip class="bg-accent" :offset="[0, 0]">
                  <strong>{{ recompensa.descricao }}</strong>
                </q-tooltip>
              </q-list>
              <div v-else class="text-h6">Nenhuma recompensa para mostrar</div>
            </q-scroll-area>
          </q-card-section>
        </q-card-section>
      </q-card>

      <div
        class="text-h5 text-secondary bg-dark text-bold q-py-md q-pl-lg my-posts"
      >
        Minhas Publicações
      </div>
      <q-infinite-scroll
        ref="inf"
        @load="onLoad"
        :offset="100"
        v-if="game_posts.length"
      >
        <q-card
          v-for="post in game_posts"
          :key="post"
          dark
          class="bg-grey-9 my-card"
        >
          <q-card-section horizontal>
            <q-card-section class="like_zone">
              <q-item>
                <q-btn
                  v-if="post.reacao == 'neutro' || post.reacao == 'dislike'"
                  flat
                  round
                  icon="thumb_up"
                  @click="likePost(post.id)"
                />
                <q-btn
                  v-if="post.reacao == 'like'"
                  flat
                  round
                  icon="thumb_up"
                  style="color: #00c230"
                  @click="likePost(post.id)"
                >
                </q-btn>
              </q-item>
              <q-item>
                <q-item-section
                  style="
                    align-items: center;
                    font-weight: bold;
                    font-size: 20px;
                    color: white;
                  "
                >
                  {{ post.likes }}
                </q-item-section>
              </q-item>
              <q-item>
                <q-btn
                  v-if="post.reacao == 'neutro' || post.reacao == 'like'"
                  flat
                  round
                  icon="thumb_down"
                  @click="dislikePost(post.id)"
                >
                </q-btn>
                <q-btn
                  v-if="post.reacao == 'dislike'"
                  flat
                  round
                  icon="thumb_down"
                  style="color: red"
                  @click="dislikePost(post.id)"
                >
                </q-btn>
              </q-item>
            </q-card-section>

            <q-separator vertical></q-separator>

            <q-card-section class="content">
              <q-item>
                <q-item-section avatar>
                  <q-avatar size="50px">
                    <q-img
                      :src="post.gamer.avatar.link"
                      class="imagem_avatar_post"
                    />
                  </q-avatar>
                </q-item-section>

                <q-item-section>
                  <q-item-label
                    style="display: flex; justify-content: space-between"
                    ><div>{{ post.gamer.nome }}</div>
                    <q-icon
                      size="20px"
                      name="delete"
                      color="red"
                      class="cursor-pointer"
                    >
                      <q-menu>
                        <q-item class="bg-dark" clickable>
                          <q-item-section
                            class="text-red remove_post"
                            @click="promptRemover(post.id)"
                          >
                            Remover Post

                            <q-dialog v-model="showConfirmation" persistent>
                              <q-card class="bg-dark">
                                <q-card-section class="row items-center">
                                  <q-avatar
                                    icon="warning"
                                    color="primary"
                                    text-color="white"
                                  />
                                  <span class="q-ml-sm text-white">
                                    Tem a certeza que quer remover a
                                    publicação?</span
                                  >
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
                                    @click="removerPost"
                                    v-close-popup
                                  />
                                </q-card-actions>
                              </q-card>
                            </q-dialog>
                          </q-item-section>
                        </q-item>
                      </q-menu>
                    </q-icon>
                  </q-item-label>
                  <q-item-label class="data">
                    {{ time_upload(post.datetime) }}
                  </q-item-label>
                  <q-item-label class="text-bold text-secondary">{{
                    post.jogo
                  }}</q-item-label>
                  <div class="zona_tags">
                    <q-item-label v-for="t in post.tags" :key="t" class="tag">
                      #{{ t.tag }}
                    </q-item-label>
                  </div>
                </q-item-section>
              </q-item>

              <q-separator />

              <q-item class="descricao">
                <div
                  v-if="post.tags.length > 0 && post.tags[0].tag == 'NEWS'"
                  class="text-h6"
                >
                  <div class="text-h6">{{ newsText(post.descricao)[0] }}</div>
                  <div class="flex text-h7">
                    <div>Para mais informações, ler&nbsp;</div>
                    <a
                      :href="newsText(post.descricao)[1]"
                      target="_blank"
                      style="color: #ffd208"
                      >artigo</a
                    >
                  </div>
                  <div style="font-size: 15px">
                    Autor: {{ newsText(post.descricao)[2] }}
                  </div>
                  <div style="font-size: 15px">
                    Fonte: {{ newsText(post.descricao)[3] }}
                  </div>
                </div>
                <div v-else class="text-h6">
                  {{ post.descricao }}
                </div>
              </q-item>

              <q-item v-if="post.multimedia">
                <q-item-section>
                  <video
                    v-if="isVideo(post.multimedia)"
                    controls
                    class="box_img"
                  >
                    <source :src="post.multimedia" type="video/mp4" />
                    Your browser does not support HTML video.
                  </video>
                  <q-img
                    v-else
                    :src="post.multimedia"
                    class="box_img cursor-pointer"
                    @click="
                      openImage = true;
                      imagePopUp = post.multimedia;
                    "
                  />
                </q-item-section>
              </q-item>
            </q-card-section>
          </q-card-section>
        </q-card>
        <q-dialog v-model="openImage">
          <q-img :src="imagePopUp" fit="contain" class="bg-dark popupimg">
            <div class="no-margin no-padding divclose">
              <q-btn
                round
                class="absolute-left-right closeimg"
                @click="openImage = false"
              >
                <q-avatar size="20px">
                  <q-icon name="close" class="closeimgicon" />
                </q-avatar>
              </q-btn>
            </div>
          </q-img>
        </q-dialog>
        <template v-slot:loading>
          <div class="row justify-center q-my-md">
            <q-spinner-dots color="white" size="40px" />
          </div>
        </template>
      </q-infinite-scroll>
      <div v-else class="text-h6 text-white q-pa-md text-bold q-mx-sm no_posts">
        Não existem posts
      </div>
    </q-scroll-area>
  </div>
</template>

<script>
import { ref } from "@vue/reactivity";
import { onMounted } from "@vue/runtime-core";
import { scroll } from "quasar";
const {
  setVerticalScrollPosition,
  getHorizontalScrollPosition,
  getVerticalScrollPosition,
} = scroll;
import axios from "axios";
import URL from "../url.js";
import { useQuasar } from "quasar";
export default {
  setup() {
    const q = useQuasar();
    const new_username = ref(null);
    const user_avatar = ref(null);
    const selected_image = ref(null);
    const changes_made = ref(false);
    const inf = ref(null);
    const game_posts = ref([]);
    const showConfirmation = ref(false);

    const saved_height = ref(0);
    const no_more_posts = ref(false);

    //variáveis aceder BD
    const utilizador = ref(null);
    const old_username = ref(null);
    const official_username = ref(null);
    const official_avatar = ref(null);

    const clickedPost = ref("");
    const removerPost = () => {
      axios({
        method: "post",
        url: URL.URL + "/posts/deletePost/" + clickedPost.value,
        params: {
          tipo_post: 0,
        },
      });
      game_posts.value = game_posts.value.filter(
        (g) => g.id != clickedPost.value
      );
      showConfirmation.value = false;
    };

    const promptRemover = (id) => {
      showConfirmation.value = true;
      clickedPost.value = id;
    };

    onMounted(async () => {
      //obter dados do utilizador(podia ser passado como props)
      const result_getPerfil = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getPerfil/" + localStorage.id,
      });

      const result_data_getPerfil = await result_getPerfil.data;
      utilizador.value = result_data_getPerfil;
      old_username.value = result_data_getPerfil.nome;
      user_avatar.value = result_data_getPerfil.avatar.link;
      official_avatar.value = result_data_getPerfil.avatar.link;
      official_username.value = utilizador.value.nome;

      const game_feed = await axios({
        method: "get",
        url:
          URL.URL +
          "/posts/multimedia/postAmigo/" +
          localStorage.id +
          "/" +
          localStorage.id +
          "/0",
      });

      const game_feed_data = await game_feed.data;
      game_posts.value = game_feed_data;
    });

    const feedscroll = ref(null);
    const scrollToTop = () => {
      const scrollArea = feedscroll.value;
      const scrollTarget = scrollArea.getScrollTarget();
      setTimeout(() => {
        setVerticalScrollPosition(scrollTarget, 0, 1000);
      }, 1);
      saved_height.value = 0;
      no_more_posts.value = false;
    };

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
      openImage: ref(false),
      q,
      imagePopUp: ref(null),
      scrollToTop,
      feedscroll,
      no_more_posts,
      saved_height,
      changes_made,
      utilizador,
      old_username,
      new_username,
      official_username,
      official_avatar,
      selected_image,
      user_avatar,
      inf,
      game_posts,
      removerPost,
      showConfirmation,
      promptRemover,
      CLOUDINARY_URL:
        "https://api.cloudinary.com/v1_1/gamehubmultimedia/upload",
      CLOUDINARY_UPLOAD_PRESET: "xpjmvfcb",
      onLoad(index, done) {
        if (index - 1 === 0) {
          done();
        } else {
          setTimeout(async () => {
            const game_feed = await axios({
              method: "get",
              url:
                URL.URL +
                "/posts/postsMediaGamer/" +
                localStorage.id +
                "/" +
                (index - 1),
            });

            const game_feed_data = await game_feed.data;
            if (game_feed_data.length == 0) {
              no_more_posts.value = true;
              done(true);
            }
            game_posts.value.push(...game_feed_data);

            done();
          }, 1000);
        }
      },
    };
  },
  methods: {
    reset_avatar() {
      if (
        this.user_avatar !=
        "https://api.multiavatar.com/" + this.official_username + ".png"
      ) {
        this.user_avatar =
          "https://api.multiavatar.com/" + this.official_username + ".png";
        this.changes_made = true;
      }
    },

    async save() {
      if (this.new_username != null) {
        //se mudou o nome
        const resp = await axios({
          method: "post",
          url:
            URL.URL +
            "/utilizador/setnomegamer/" +
            localStorage.id +
            "/" +
            this.new_username,
        });

        if (resp.data == false) {
          //nome já existia
          this.q.notify({
            progress: true,
            message:
              "Username já existe. Por favor introduza um nome diferente",
            color: "red",
            position: "bottom-right",
          });
        } else {
          //se nome não existe

          if (
            this.official_avatar != this.user_avatar &&
            this.selected_image != null
          ) {
            //se também mudou avatar
            if (this.user_avatar != null) {
              await axios({
                method: "post",
                url: URL.URL + "/utilizador/setavatargamer/" + localStorage.id,
                params: {
                  link: this.user_avatar,
                },
              });

              this.q.notify({
                progress: true,
                message: "Alterações guardadas com sucesso!",
                color: "green",
                position: "bottom-right",
              });

              this.$emit("novo_logo", this.user_avatar);
              this.$emit("novo_username", this.new_username);
              this.utilizador.nome = this.new_username;

              this.changes_made = false;
              this.selected_image = null;
              this.official_username = this.new_username;
              this.new_username = null;
            } else {
              this.q.notify({
                progress: true,
                message: "Por favor selecione um avatar válido!",
                color: "red",
                position: "bottom-right",
              });
            }
          } else {
            this.q.notify({
              progress: true,
              message: "Username atualizado com sucesso",
              color: "green",
              position: "bottom-right",
            });

            this.$emit("novo_username", this.new_username);
            this.utilizador.nome = this.new_username;
            this.official_username = this.new_username;
            this.new_username = null;
            this.changes_made = false;
          }
        }
      } 
      else {
        if (
          this.official_avatar != this.user_avatar &&
          this.user_avatar != null
        ) {
          await axios({
            method: "post",
            url: URL.URL + "/utilizador/setavatargamer/" + localStorage.id,
            params: {
              link: this.user_avatar,
            },
          });

          this.$emit("novo_logo", this.user_avatar);
          this.changes_made = false;
          this.selected_image = null;
          this.q.notify({
            progress: true,
            message: "Avatar atualizado com sucesso!",
            color: "green",
            position: "bottom-right",
          });
        } else {
          this.q.notify({
            progress: true,
            message: "Por favor selecione um avatar válido!",
            color: "red",
            position: "bottom-right",
          });
          this.changes_made = false;
        }
      }
    },

    cancel() {
      this.$router.go(-1);
    },
    isVideo(multimedia) {
      const last = multimedia.split(".").pop();

      if (last == "mp4" || last == "mp3") return true;
      else return false;
    },

    time_upload(data) {
      const data_publicacao = new Date(data);
      const data_atual = Date.now();
      const diff = data_atual - data_publicacao;

      //const segundos
      const valor_segundos = (diff / 1000).toFixed(0);

      if (valor_segundos < 60) {
        if (valor_segundos < 30) {
          return "Agora mesmo";
        } else {
          return "Há " + valor_segundos + " segundos";
        }
      } else {
        //em minutos
        const valor_minutos = (Math.abs(diff) / 1000 / 60).toFixed(0);

        if (valor_minutos < 60) {
          return "Há " + valor_minutos + " minutos";
        } else {
          //em horas
          const valor_horas = (Math.abs(diff) / 36e5).toFixed(0);

          if (valor_horas == 1) {
            return "Há " + valor_horas + " hora";
          }

          if (valor_horas < 24) {
            return "Há " + valor_horas + " horas";
          } else {
            //em dias
            const valor_dias = (diff / (1000 * 3600 * 24)).toFixed(0);

            if (valor_dias < 2) return "Há " + valor_dias + " dia";
            else return "Há " + valor_dias + " dias";
          }
        }
      }
    },

    async likePost(id) {
      const btn = this.game_posts.filter((p) => p.id == id)[0];

      if (btn.reacao == "like") {
        (await axios({
          method: "post",
          url: URL.URL + "/posts/like/remove/" + id + "/" + localStorage.id,
        })) *
          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "neutro";
              p.likes -= 1;
            });
      } else {
        if (btn.reacao == "neutro") {
          await axios({
            method: "post",
            url: URL.URL + "/posts/like/" + id + "/" + localStorage.id,
          });
          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "like";
              p.likes += 1;
            });
        } else {
          await axios({
            method: "post",
            url: URL.URL + "/posts/like/" + id + "/" + localStorage.id,
          });

          await axios({
            method: "post",
            url: URL.URL + "/posts/like/" + id + "/" + localStorage.id,
          });

          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "like";
              p.likes += 2;
            });
        }
        this.q.notify({
          progress: true,
          message: "Like Registado com Sucesso",
          color: "green",
          position: "bottom-right",
        });
      }
    },
    async dislikePost(id) {
      const btn = this.game_posts.filter((p) => p.id == id)[0];

      if (btn.reacao == "dislike") {
        await axios({
          method: "post",
          url: URL.URL + "/posts/dislike/remove/" + id + "/" + localStorage.id,
        });
        this.game_posts
          .filter((p) => p.id == id)
          .forEach((p) => {
            p.reacao = "neutro";
            p.likes += 1;
          });
      } else {
        if (btn.reacao == "neutro") {
          await axios({
            method: "post",
            url: URL.URL + "/posts/dislike/" + id + "/" + localStorage.id,
          });

          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "dislike";
              p.likes -= 1;
            });
        } else {
          await axios({
            method: "post",
            url: URL.URL + "/posts/dislike/" + id + "/" + localStorage.id,
          });

          await axios({
            method: "post",
            url: URL.URL + "/posts/dislike/" + id + "/" + localStorage.id,
          });

          this.game_posts
            .filter((p) => p.id == id)
            .forEach((p) => {
              p.reacao = "dislike";
              p.likes -= 2;
            });
        }
        this.q.notify({
          progress: true,
          message: "Dislike Registado com Sucesso",
          color: "green",
          position: "bottom-right",
        });
      }
    },
    newsText(text) {
      const res = text.split("\n");
      return res;
    },
    updateSavedHeight() {
      const scrollArea = this.feedscroll;
      const scrollTarget = scrollArea.getScrollTarget();
      this.saved_height = getVerticalScrollPosition(scrollTarget);
    },
  },
  watch: {
    selected_image: async function () {
      if (this.selected_image != null) {
        var formData = new FormData();
        formData.append("file", this.selected_image);
        formData.append("upload_preset", this.CLOUDINARY_UPLOAD_PRESET);

        var g = await axios({
          url: this.CLOUDINARY_URL,
          method: "POST",
          headers: {
            "Content-Type": "application/x-www-form-urlencoded",
          },
          data: formData,
        });

        var g_data = await g.data;
        this.user_avatar = g_data.secure_url;
        this.changes_made = true;
      } else {
        if (this.changes_made){
          this.q.notify({
            progress: true,
            message: "Mudança de avatar anulada!",
            color: "red",
            position: "bottom-right",
          });
          if (this.new_username == null) this.changes_made = false;
        }
      }
    },
    new_username: function () {
      if (this.new_username != null && this.new_username != "")
        this.changes_made = true;
      else {
        this.changes_made = false;
      }
    },

    saved_height(newVal) {
      if (newVal > 2600)
        document.getElementById("button_scrollTop").style.display = "block";
      else document.getElementById("button_scrollTop").style.display = "none";
    },

    no_more_posts(newVal) {
      if (newVal == true) {
        this.q.notify({
          progress: true,
          message: "Não há mais Posts para Mostrar",
          color: "grey",
          position: "bottom-right",
        });
      }
    },
  },
};
</script>

<style scoped>
.box {
  margin-bottom: -30px;
}

.areaPosts {
  height: 92vh;
}

.profile_card {
  width: 80%;
  margin: auto;
  margin-top: 5%;
  margin-bottom: 2%;
}

.left_zone {
  text-align: center;
  background: #1d1d1d;
  margin-top: 1%;
}

.right_zone {
  width: 80%;
  height: 500px;
  background: #1d1d1d;
}

.upload_file {
  margin: 20px auto;
  border-radius: 5pt;
  background: #222222;
  max-width: 200px;
}

.upload_file label {
  width: 600px;
}

.reset_avatar {
  width: 150px;
  height: 20px;
  font-size: 12px;
  margin-top: 10px;
  font-weight: bold;
}

.reset_avatar:disabled {
  background: grey;
}

.reset_avatar:hover {
  transform: scale(1.05);
}

.change_avatar {
  margin-top: 20px;
  background: grey;
  width: 50%;
}

.username {
  font-weight: bold;
  margin-top: -20px;
}

.area_recompensas {
  height: 80%;
  padding: 20px;
  background: #222222;
  border-radius: 10px;
}

.recompensa_card {
  color: white;
  padding-left: 10px;
  padding-top: 5px;
  padding-bottom: 1px;
  margin-bottom: 20px;
  border-radius: 15px;
}

.titulo {
  font-weight: bold;
  font-size: 18px;
}

.avaliacao {
  margin-bottom: 10px;
  font-weight: bold;
}

.icon_e_titulo {
  margin-top: 1%;
  margin-left: 2%;
}

.recompensa {
  margin-top: 1%;
  margin-left: 2%;
  font-weight: bold;
  font-size: 20px;
}

.buttons {
  margin-top: 10px;
}

.button_cancel {
  background: red;
  color: white;
  font-weight: bold;
  margin-bottom: 10px;
}

.button_cancel:hover {
  transform: scale(1.1);
}

.button_save {
  background: #005cc5;
  font-weight: bold;
}

.button_save:disabled {
  background: grey;
}

.button_save:hover {
  transform: scale(1.1);
}

.imagem_avatar {
  width: 100px;
  height: 100px;
}

.my-card {
  width: 80%;
  margin: 15px auto;
  align-items: center;
  border-radius: 20px;
}
.like_zone {
  background: rgb(32, 32, 32);
  align-items: center;
}

.like_number {
  align-items: center;
  font-weight: bold;
  font-size: 20px;
  margin-top: -40px;
}

.content {
  width: 100%;
}

.imagem_avatar_post {
  width: 50px;
  height: 50px;
}

.data {
  font-size: 12px;
}

.zona_tags {
  display: flex;
}

.tag {
  margin-right: 10px;
  margin-top: 5px;
  border-radius: 10px;
  font-size: 15px;
  color: #ffd208;
  cursor: pointer;
  background: #1d1d1d;
  padding: 5px;
}

.tag:hover {
  transform: scale(1.05);
}

.descricao {
  color: white;
  word-break: break-all;
  hyphens: auto;
  white-space: pre-line;
}

.box_img {
  max-width: 100%;
  max-height: 500px;
  border-radius: 10px;
}

.remove_post:hover {
  transform: scale(1.05);
  font-weight: bold;
  text-decoration: underline;
}

.my-posts {
  width: 80%;
  margin: 15px auto;
  align-items: center;
  border-radius: 20px;
}

.card_recompensa {
  background: #1d1d1d;
  border-radius: 10px;
  justify-content: center;
  padding-top: 10px;
}

.nome_recompensa {
  margin-top: 0.5%;
  margin-left: 2%;
  font-weight: bold;
  font-size: 15px;
}

.no_posts {
  width: 80%;
  margin: auto;
  margin-top: 10px;
}

.btn_top {
  position: fixed;
  z-index: 10;
  margin-top: 1%;
  margin-left: 38%;
  background: #005cc5;
  color: white;
  font-weight: bold;
  display: none;
  opacity: 0.9;
}

.btn_top:hover {
  transform: scale(1.05);
}

.popupimg {
  max-width: 80%;

  width: 100%;
  border-radius: 20px;
  overflow: hidden;
}

.closeimg {
  background-color: rgba(1, 1, 1, 0.5);
}

.closeimgicon {
  color: #ffd208;
}

.divclose {
  background-color: rgba(0, 0, 0, 0);
}

@media only screen and (max-height: 900px) {
  .areaPosts {
    height: 90vh;
  }
}
</style>
