<template>
  <q-layout class="zona_centro" view="hHh LpR fFf">
    <q-header elevated class="bg-primary text-secondary">
      <q-toolbar>
        <q-btn
          dense
          flat
          round
          class="btn_open_games"
          @click="toggleLeftDrawer"
        >
          <q-icon name="sports_esports"></q-icon>
        </q-btn>
        <q-toolbar-title class="title">
          <q-btn
            dense
            flat
            class="btn_logo"
            to="/main"
            @click="selectedGame = ''"
          >
            <img src="../assets/logo.png" id="logo" />
          </q-btn>
        </q-toolbar-title>

        <q-btn-dropdown class="btn_small_devices" dropdown-icon="menu">
          <q-list class="bg-dark">
            <q-item
              class="text-secondary"
              clickable
              v-close-popup
              to="/createPost"
              @click="selectedGame = ''"
            >
              <q-item-section>
                <q-item-label>Criar Publicação</q-item-label>
              </q-item-section>
            </q-item>

            <q-item
              class="text-secondary"
              clickable
              v-close-popup
              to="/createGroup"
              @click="selectedGame = ''"
            >
              <q-item-section>
                <q-item-label>Criar Grupo</q-item-label>
              </q-item-section>
            </q-item>

            <q-item
              class="text-secondary"
              clickable
              v-close-popup
              to="/joinTeam"
              @click="selectedGame = ''"
            >
              <q-item-section>
                <q-item-label>Procurar grupo</q-item-label>
              </q-item-section>
            </q-item>
          </q-list>
        </q-btn-dropdown>

        <q-btn class="btn_post" to="/createPost" @click="selectedGame = ''">
          Criar Publicação
        </q-btn>

        <q-btn
          class="btn_jointeam"
          to="/createGroup"
          @click="selectedGame = ''"
        >
          Criar Grupo
        </q-btn>

        <q-btn class="btn_jointeam" to="/joinTeam" @click="selectedGame = ''">
          Procurar Grupo
        </q-btn>

        <q-btn
          dense
          flat
          round
          class="btn_open_groups"
          @click="toggleRightDrawer"
        >
          <q-icon name="groups"></q-icon>
        </q-btn>
      </q-toolbar>
    </q-header>

    <!--Sidebar com os jogos-->
    <q-drawer
      v-model="leftDrawerOpen"
      show-if-above
      elevated
      :width="100"
      :breakpoint="500"
      class="bg-dark"
    >
      <q-scroll-area
        :thumb-style="thumbStyle"
        :bar-style="barStyle"
        style="height: 200px; max-width: 300px"
        class="fit"
      >
        <q-list padding class="menu-list">
          <q-item>
            <q-btn
              round
              size="20px"
              clickable
              class="button_add_game"
              to="/gamesList"
              @click="selectedGame = ''"
              exact
            >
              <q-icon name="add"></q-icon>
            </q-btn>
            <q-tooltip
              class="bg-accent"
              anchor="center start"
              self="center right"
              :offset="[-15, -15]"
            >
              <strong>Adicionar Jogo</strong>
            </q-tooltip>
          </q-item>

          <q-item v-for="g in myGames" :key="g.id">
            <div v-if="selectedGame == g.nome" class="selected-div">
              <div class="selected" />
              <GameLogo
                :link="g.bannerLink"
                :nome="g.nome"
                :gameid="g.id"
                @selectGame="(s) => (selectedGame = s)"
                @stopFollowing="(id) => removeGame(id, 1)"
              />
            </div>
            <div v-else class="selected-div">
              <GameLogo
                :link="g.bannerLink"
                :nome="g.nome"
                :gameid="g.id"
                @selectGame="(s) => (selectedGame = s)"
                @stopFollowing="(id) => removeGame(id, 0)"
              />
            </div>
          </q-item>
        </q-list>
      </q-scroll-area>
    </q-drawer>

    <!--Sidebar com os amigos-->
    <q-drawer
      show-if-above
      v-model="rightDrawerOpen"
      elevated
      :width="300"
      :breakpoint="500"
      side="right"
      class="bg-dark full-height"
    >
      <q-item class="item_profile">
        <q-item-section avatar class="item_section_profile">
          <q-avatar size="50px" class="profile">
            <q-img v-if="user" :src="user.avatar.link" class="imagem_avatar" />
            <q-spinner v-else color="secondary" size="3em" />
            <q-menu
              transition-show="rotate"
              transition-hide="rotate"
              class="bg-primary"
            >
              <div class="row no-wrap q-pa-md">
                <q-list>
                  <q-item
                    clickable
                    v-close-popup
                    class="ver_perfil_item"
                    to="/profile"
                    @click="selectedGame = ''"
                  >
                    <q-item-section>Ver Perfil</q-item-section>
                  </q-item>

                  <q-separator />

                  <q-item
                    class="log_out_item"
                    clickable
                    @click="logout"
                    v-close-popup
                  >
                    <q-item-section>Log Out</q-item-section>
                  </q-item>
                </q-list>
              </div>
            </q-menu>
          </q-avatar>
        </q-item-section>
        <q-item-section v-if="user">
          <q-item-label class="user_name">{{ user.nome }}</q-item-label>
        </q-item-section>
        <q-item-section v-else>
          <q-spinner color="secondary" size="3em" />
        </q-item-section>
      </q-item>

      <q-item-label header>Grupo</q-item-label>

      <q-card dark class="group_card" v-if="grupo && myGames">
        <q-item
          :style="{
            backgroundImage: 'url(' + imageLink + ')',
          }"
          clickable
          class="zona_cima_grupo q-pr-xs q-pt-xs"
          @click="
            groupchat = true;
            chat = false;
          "
        >
          <q-item-section avatar>
            <q-icon name="groups"></q-icon>
          </q-item-section>

          <q-item-section style="margin-left: -20px">
            <q-item-label>{{ grupo.postGrupo.nomeEquipa }}</q-item-label>
          </q-item-section>

          <q-icon
            name="close"
            class="my-icon"
            @click.capture.stop="confirm = true"
          ></q-icon>
          <q-dialog v-model="confirm" persistent>
            <q-card class="bg-dark">
              <q-card-section class="row items-center">
                <q-avatar icon="warning" color="primary" text-color="white" />
                <span class="q-ml-sm text-white">
                  Tem a certeza que quer sair do grupo?</span
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
                  @click="sairGrupo"
                  v-close-popup
                />
              </q-card-actions>
            </q-card>
          </q-dialog>
        </q-item>

        <q-card class="users_in_group q-pa-none">
          <q-card-section v-if="grupo" horizontal>
            <q-item v-if="grupo.gamers.length > 4">
              <q-item-section
                v-for="u in grupo.gamers.slice(0, 4)"
                :key="u.id"
                class="user_in_group"
              >
                <q-avatar
                  class="friend_avatar"
                  round
                  size="40px"
                  @click="viewFriendProfile(u.id)"
                >
                  <q-img
                    :src="u.avatar.link"
                    style="width: 40px; height: 40px"
                  />
                </q-avatar>
                <q-tooltip class="bg-accent" :offset="[10, 10]">
                  <strong>{{ u.nome }}</strong>
                </q-tooltip>
              </q-item-section>
              <q-item-section class="q-px-s more" @click="seemore = true">
                + {{ grupo.gamers.length - 4 }}</q-item-section
              >
              <q-dialog v-model="seemore">
                <q-card class="bg-dark">
                  <q-card-section>
                    <div class="text-h6 text-white">
                      Grupo {{ grupo.nomegrupo }}
                    </div>
                  </q-card-section>

                  <q-card-section>
                    <q-list>
                      <q-item
                        clickable
                        v-ripple
                        v-for="u in grupo.gamers"
                        :key="u"
                        class="row"
                        @click="viewFriendProfile(u.id)"
                      >
                        <q-avatar class="friend_avatar" round size="40px">
                          <q-img
                            :src="u.avatar.link"
                            style="width: 40px; height: 40px"
                          />
                        </q-avatar>
                        <q-item-section class="text-white">{{
                          u.nome
                        }}</q-item-section>
                      </q-item>
                    </q-list>
                    <q-item-section> </q-item-section>
                  </q-card-section>

                  <q-card-actions align="right">
                    <q-btn flat label="OK" color="white" v-close-popup />
                  </q-card-actions>
                </q-card>
              </q-dialog>
            </q-item>
            <q-item v-else>
              <q-item-section
                v-for="u in grupo.gamers"
                :key="u"
                class="user_in_group"
              >
                <q-avatar
                  class="friend_avatar"
                  round
                  size="40px"
                  @click="viewFriendProfile(u.id)"
                >
                  <q-img
                    :src="u.avatar.link"
                    style="width: 40px; height: 40px"
                  />
                </q-avatar>
                <q-tooltip class="bg-accent" :offset="[10, 10]">
                  <strong>{{ u.nome }}</strong>
                </q-tooltip>
              </q-item-section>
            </q-item>
          </q-card-section>
          <q-item-section v-else>
            <q-spinner color="secondary" size="3em" />
          </q-item-section>
        </q-card>
      </q-card>
      <q-card v-else dark class="group_card">
        <q-item class="no-group">
          <q-item-section>
            <q-item-label>Ainda não está em nenhum grupo.</q-item-label>
          </q-item-section>
        </q-item>
      </q-card>

      <q-separator dark inset class="divide_box" />

      <q-item-label header class="amigos_text">
        <div class="amigos_header">
          Amigos
          <q-btn round flat>
            <q-icon
              name="add_circle"
              color="secondary"
              @click="addfriend = true"
            ></q-icon>
          </q-btn>
          <q-dialog v-model="addfriend">
            <q-card class="bg-dark friend-modal">
              <q-card-section>
                <div class="text-h6 text-white">Adicionar amigo</div>
              </q-card-section>

              <q-card-section class="q-pt-none row">
                <q-input
                  outlined
                  color="secondary"
                  v-model="friendusername"
                  label="Insira o username"
                  input-style="color:white"
                  label-color="secondary"
                  class="col col-md-8 col-xs-12"
                >
                  <template v-slot:prepend>
                    <q-icon name="search" color="secondary" />
                  </template>
                </q-input>
                <q-btn
                  class="col-6 col-md-4 col-xs-12 text-black add_friend_buttons"
                  color="secondary"
                  label="Adicionar"
                  @click="adicionaAmigo(friendusername)"
                >
                  <q-popup-proxy v-if="feedback">
                    <q-banner
                      :class="
                        feedback.type == 'success' ? 'bg-green-9' : 'bg-red-9'
                      "
                    >
                      <template v-slot:avatar>
                        <q-icon
                          :name="feedback.type == 'success' ? 'done' : 'error'"
                          color="primary"
                        />
                      </template>
                      {{ feedback.text }}
                    </q-banner>
                  </q-popup-proxy>
                </q-btn>
              </q-card-section>

              <q-separator dark inset />

              <q-card-section>
                <div class="text-h7 q-px-md text-weight-bold text-white">
                  Amigos sugeridos
                </div>
              </q-card-section>

              <q-card-section v-if="suggestedFriends.length">
                <q-chip
                  clickable
                  v-for="u in suggestedFriends"
                  :key="u.id"
                  icon="add"
                  @click="setAmigo(u.nome)"
                  >{{ u.nome }}
                </q-chip>
              </q-card-section>
              <q-card-section v-else>
                <div class="text-subtitle2 q-px-md text-white">
                  Não há sugestões disponíveis...
                </div>
              </q-card-section>

              <q-card-actions align="right">
                <q-btn
                  flat
                  style="background: red"
                  class="add_friend_buttons"
                  label="Fechar"
                  color="white"
                  v-close-popup
                />
              </q-card-actions>
            </q-card>
          </q-dialog>
        </div>
      </q-item-label>

      <q-input
        v-if="user && user.amigos.length > 0"
        class="input_procurar"
        color="secondary"
        filled
        label-color="secondary"
        v-model="friend"
        :input-style="{ color: 'white' }"
        label="Procurar Amigo"
      >
        <template v-slot:prepend>
          <q-icon name="search" color="secondary" />
        </template>
      </q-input>

      <q-scroll-area
        v-if="user && user.amigos.length"
        :thumb-style="thumbStyle"
        :bar-style="barStyle"
        style="max-width: 300px"
        class="box_amigos"
      >
        <q-list padding class="menu-list lista_amigos">
          <q-card
            dark
            v-for="amigo in filteredFriends"
            :key="amigo.id"
            class="friend_card"
            @click="openChat(amigo)"
          >
            <q-item>
              <q-item-section
                avatar
                v-if="
                  notificacoes.length > 0 && getNotificacoes(amigo.id) !== false
                "
              >
                <q-avatar size="40px">
                  <q-img
                    :src="amigo.avatar.link"
                    style="width: 40px; height: 40px"
                  />
                  <q-badge
                    v-if="
                      getNotificacoes(amigo.id)[0]
                        .numero_mensagens_nao_lidas !== 0
                    "
                    floating
                    :color="amigo.estado == 'Online' ? 'green' : 'accent'"
                    rounded
                    >{{
                      getNotificacoes(amigo.id)[0].numero_mensagens_nao_lidas
                    }}
                  </q-badge>
                  <q-badge
                    v-else
                    floating
                    :color="amigo.estado == 'Online' ? 'green' : 'grey'"
                    rounded
                  />
                </q-avatar>
              </q-item-section>

              <q-item-section>
                <q-item-label>{{ amigo.nome }}</q-item-label>
              </q-item-section>
              <q-menu transition-show="rotate"
                transition-hide="rotate"
                class="bg-primary" context-menu>
                <q-list style="padding: 20px;">
                  <q-item
                    clickable
                    v-close-popup
                    class="ver_perfil_item"
                    @click="viewFriendProfile(amigo.id)">
                    <q-item-section>Ver Perfil</q-item-section>
                  </q-item>

                  <q-separator />

                  <q-item
                    class="text-white log_out_item"
                    clickable
                    v-close-popup
                    @click="id_friend_to_remove = amigo.id" >
                    <q-item-section>Remover Amigo</q-item-section>
                  </q-item>
                </q-list>
              </q-menu>
            </q-item>
          </q-card>
        </q-list>
      </q-scroll-area>
      <q-card v-else dark class="group_card">
        <q-item class="no-group">
          <q-item-section>
            <q-item-label>Ainda não adicionou nenhum amigo.</q-item-label>
          </q-item-section>
        </q-item>
      </q-card>
    </q-drawer>

    <!--Zona principal-->
    <q-page-container>
      <router-view
        :myGames="myGames"
        v-on:gamesToAdd="getGamesToAdd"
        v-on:novo_logo="
          (l) => {
            newLogo(l);
          }
        "
        v-on:novo_username="(n) => (user.nome = n)"
        v-on:friend_to_remove="(i) => (id_friend_to_remove = i)"
        v-on:friend_to_add="(i) => (nome_friend_to_add = i)"
        v-on:joinedGroup="joinedGroup"
        v-on:setSelectedGame="
          (n) => {
            setSelectedGame(n);
          }
        "
        v-on:stopFollowing="(id) => removeGame(id, 1)"
      />
      <transition
        appear
        enter-active-class="animated slideInRight"
        leave-active-class="animated slideOutRight"
      >
        <MessageChat
          v-if="chat"
          :chat="chat"
          :myavatar="user.avatar.link"
          @closeChat="chat = null"
          class="chat"
        />
      </transition>
      <transition
        appear
        enter-active-class="animated slideInRight"
        leave-active-class="animated slideOutRight"
      >
        <GroupChat
          v-if="groupchat"
          :idGrupo="grupoId"
          @closeChat="groupchat = false"
          class="chat"
        />
      </transition>
    </q-page-container>
  </q-layout>
</template>

<script>
import { ref } from "vue";
import { computed, onMounted, onBeforeUnmount } from "@vue/runtime-core";
import GameLogo from "../components/GameLogo.vue";
import MessageChat from "../components/MessageChat.vue";
import GroupChat from "../components/GroupChat.vue";
import { useRouter } from "vue-router";
import axios from "axios";
import URL from "../url.js";
import { useQuasar } from "quasar";
export default {
  name: "MainLayout",
  components: { GameLogo, MessageChat, GroupChat },
  setup() {
    const q = useQuasar();
    const router = useRouter();
    const selectedGame = ref("");
    const confirm = ref(false);
    const chat = ref(null);
    const groupchat = ref(false);
    const leftDrawerOpen = ref(false);
    const rightDrawerOpen = ref(false);
    const addfriend = ref(false);
    const friendusername = ref("");
    const seemore = ref(false);
    const id_friend_to_remove = ref(null);
    const nome_friend_to_add = ref(null);
    const imageLink = ref(null);

    if (localStorage.getItem("id") == null) {
      window.location.replace("/");
    }

    //dados obtidos da base de dados
    const user = ref(null);
    const grupo = ref(null);
    const grupoId = ref("null");
    const myGames = ref(null);
    const notificacoes = ref([]);
    var interval = ref("");

    onMounted(async () => {
      //obter info do utilizador
      const result_getPerfil = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getPerfil/" + localStorage.id,
      });
      const result_data_getPerfil = await result_getPerfil.data;
      user.value = result_data_getPerfil;

      //obter grupo do utilizador
      const user_grupoID = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getGrupoID/" + localStorage.id,
      });

      const user_grupoID_data = await user_grupoID.data;
      grupoId.value = user_grupoID_data;

      const user_grupo = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getGrupo/" + user_grupoID_data,
      });

      const user_grupo_data = await user_grupo.data;
      grupo.value = user_grupo_data;
      imageLink.value = user_grupo_data.imageLink;

      //obter jogos que user já tem
      const user_jogos = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getListaJogosSeguir/" + localStorage.id,
      });

      const user_jogos_data = await user_jogos.data;
      myGames.value = user_jogos_data;

      const result_notificacoes = await axios({
        method: "get",
        url:
          URL.URL +
          "/utilizador/getNumMensagensNaoLidasAmigo/" +
          localStorage.id,
      });
      const result_data_notificacoes = await result_notificacoes.data;
      notificacoes.value = result_data_notificacoes;
      interval.value = setInterval(async () => {
        const result_notificacoes = await axios({
          method: "get",
          url:
            URL.URL +
            "/utilizador/getNumMensagensNaoLidasAmigo/" +
            localStorage.id,
        });
        const result_data_notificacoes = await result_notificacoes.data;

        if (
          notificacoes.value.filter(
            (n, index) =>
              n.numero_mensagens_nao_lidas <
              result_data_notificacoes[index].numero_mensagens_nao_lidas
          ).length > 0
        ) {
          var audio = new Audio(
            "https://notificationsounds.com/storage/sounds/file-sounds-1135-deduction.mp3"
          );
          audio.play();
          notificacoes.value
            .filter(
              (n, index) =>
                n.numero_mensagens_nao_lidas <
                result_data_notificacoes[index].numero_mensagens_nao_lidas
            )
            .forEach((n) => {
              console.log(n);
              q.notify({
                progress: true,
                message:
                  "Recebeu uma mensagem de " +
                  user.value.amigos.filter((a) => a.id == n.id_amigo)[0].nome,
                color: "green",
                position: "bottom-right",
              });
            });
        }
        notificacoes.value = result_data_notificacoes;
      }, 10000);
    });

    const getNotificacoes = (id) => {
      if (notificacoes.value.some((e) => e.id_amigo === id)) {
        return notificacoes.value.filter((obj) => {
          return obj.id_amigo === id;
        });
      } else return false;
    };

    onBeforeUnmount(() => {
      clearInterval(interval.value);
    });

    const logout = () => {
      axios({
        method: "post",
        url: URL.URL + "/utilizador/logout/" + localStorage.id,
      });
      localStorage.removeItem("id");
      router.push("/login");
    };

    const removeGame = (id, selected) => {
      console.log(myGames.value);
      console.log(id);
      myGames.value = myGames.value.filter((g) => g.id != id);
      console.log(myGames.value);

      axios({
        method: "post",
        url: URL.URL + "/utilizador/stopJogoSeguir/" + localStorage.id,
        params: {
          id_jogo: id,
        },
      });

      if (selected) {
        router.push("/main");
      }
    };

    const friend = ref("");
    const filteredFriends = computed(() => {
      return user.value.amigos.filter((u) =>
        u.nome.toLowerCase().includes(friend.value.toLowerCase())
      );
    });

    const openChat = (amigo) => {
      groupchat.value = false;
      var objIndex = notificacoes.value.findIndex(
        (obj) => obj.id_amigo == amigo.id
      );
      notificacoes.value[objIndex].numero_mensagens_nao_lidas = 0;
      chat.value = amigo;
    };

    const onClickOutside = () => {
      chat.value = "";
    };

    const linkTo = (game) => {
      const g = game.replace(/ /g, "");
      return require("../assets/banners/" + g + ".png");
    };

    const feedback = ref({
      text: "Campo vazio.",
      type: "",
    });

    const suggestedFriends = computed(() => {
      if (grupo.value) {
        return grupo.value.gamers.filter(
          (u) =>
            !user.value.amigos.some((e) => e.nome === u.nome) &&
            u.id != localStorage.id
        );
      } else {
        return [];
      }
    });

    const adicionaAmigo = async (amigo) => {
      if (amigo == user.value.nome) {
        feedback.value = {
          text: "Não pode adicionar-se a si mesmo.",
          type: "error",
        };
      } else if (amigo != "") {
        const result = await axios({
          method: "post",
          url:
            URL.URL +
            "/utilizador/adicionaramigo/" +
            localStorage.id +
            "/" +
            amigo,
        });

        const result_data = await result.data;
        if (result_data == 2) {
          //nao existe
          feedback.value = {
            text: "O utilizador não existe.",
            type: "error",
          };
        }
        if (result_data == 1) {
          //adiciona
          feedback.value = {
            text: "Utilizador adicionado com sucesso.",
            type: "success",
          };

          const result_getPerfil = await axios({
            method: "get",
            url: URL.URL + "/utilizador/getPerfil/" + localStorage.id,
          });
          const result_data_getPerfil = await result_getPerfil.data;
          user.value = result_data_getPerfil;
          const result_notificacoes = await axios({
            method: "get",
            url:
              URL.URL +
              "/utilizador/getNumMensagensNaoLidasAmigo/" +
              localStorage.id,
          });
          const result_data_notificacoes = await result_notificacoes.data;
          notificacoes.value = result_data_notificacoes;
        }
        if (result_data == 3) {
          //ja sao amigos
          feedback.value = {
            text: "O utilizador já é seu amigo.",
            type: "error",
          };
        }
        friendusername.value = "";
      }
    };

    const setAmigo = (nome) => {
      friendusername.value = nome;
    };

    const sairGrupo = () => {
      axios({
        method: "post",
        url: URL.URL + "/utilizador/sairGrupo/" + localStorage.id,
      });
      grupo.value = null;
      confirm.value = false;
      groupchat.value = false;
    };

    const joinedGroup = async () => {
      const user_grupoID = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getGrupoID/" + localStorage.id,
      });

      const user_grupoID_data = await user_grupoID.data;
      grupoId.value = user_grupoID_data;

      const user_grupo = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getGrupo/" + user_grupoID_data,
      });

      const user_grupo_data = await user_grupo.data;
      grupo.value = user_grupo_data;
      imageLink.value = user_grupo_data.imageLink;
    };

    const newLogo = (l) => {
      user.value.avatar.link = l;
      if (grupo.value){
        grupo.value.gamers.map((el) =>
          el.id === localStorage.id ? (el.avatar.link = l) : el
        );
      }
    };

    const setSelectedGame = (n) => {
      selectedGame.value = n;
      router.push("/feed/" + myGames.value.filter((g) => g.nome === n)[0].id);
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
      leftDrawerOpen,
      toggleLeftDrawer() {
        leftDrawerOpen.value = !leftDrawerOpen.value;
      },
      rightDrawerOpen,
      toggleRightDrawer() {
        rightDrawerOpen.value = !rightDrawerOpen.value;

        /*
        var d = document.getElementsByClassName('chat')

        if (d[0]){
          if (rightDrawerOpen.value) d[0].style.marginLeft = "-275px";
          else d[0].style.marginLeft = "10px";
        } */
      },
      imageLink,
      friend,
      filteredFriends,
      linkTo,
      selectedGame,
      removeGame,
      openChat,
      groupchat,
      chat,
      onClickOutside,
      confirm,
      user,
      logout,
      grupo,
      grupoId,
      myGames,
      addfriend,
      friendusername,
      adicionaAmigo,
      suggestedFriends,
      feedback,
      setAmigo,
      seemore,
      id_friend_to_remove,
      nome_friend_to_add,
      sairGrupo,
      getNotificacoes,
      notificacoes,
      joinedGroup,
      newLogo,
      setSelectedGame,
    };
  },
  methods: {
    getGamesToAdd(result) {
      if (!this.myGames) {
        this.myGames = result;
      } else {
        result.forEach((g) =>
          this.myGames.some((el) => el.id === g.id)
            ? null
            : this.myGames.push(g)
        );
      }
    },

    viewFriendProfile(id) {
      this.selectedGame = "";

      if (id == localStorage.id) {
        this.$router.push("/profile");
      } else {
        this.$router.push("/friendProfile/" + id);
      }
    },
  },
  watch: {
    id_friend_to_remove: async function () {
      if (this.id_friend_to_remove) {
        await axios({
          method: "post",
          url: URL.URL + "/utilizador/removeramigo/" + localStorage.id,
          params: {
            id_amigo: this.id_friend_to_remove,
          },
        });

        this.user.amigos = this.filteredFriends.filter(
          (u) => u.id !== this.id_friend_to_remove
        );
      }
      this.id_friend_to_remove = "";
    },

    nome_friend_to_add: async function () {
      if (this.nome_friend_to_add) {
        await axios({
          method: "post",
          url:
            URL.URL +
            "/utilizador/adicionaramigo/" +
            localStorage.id +
            "/" +
            this.nome_friend_to_add,
        });

        const result_getPerfil = await axios({
          method: "get",
          url: URL.URL + "/utilizador/getPerfil/" + localStorage.id,
        });
        const result_data_getPerfil = await result_getPerfil.data;
        this.user = result_data_getPerfil;
      }

      this.nome_friend_to_add = "";
    },
  },
};
</script>

<style scoped>
.zona_centro {
  background: #222222;
  background-size: 100% 100%;
  animation: gradient 15s ease infinite;
}

@keyframes gradient {
  0% {
    background-position: 0% 50%;
  }
  50% {
    background-position: 100% 50%;
  }
  100% {
    background-position: 0% 50%;
  }
}

/*
.zona_centro {
  background-image: linear-gradient(160deg, #1d1d1d 45%, #222222 40%);
}*/

#logo {
  width: 100px;
  margin-left: 10px;
  margin-top: 10px;
}

.button_add_game {
  background: rgb(0, 92, 197);
  color: white;
}

.button_add_game:hover {
  border-radius: 40%;
  transform: scale(1.1);
  background: white;
  color: rgb(0, 92, 197);
}

.selected {
  height: 58px;
  width: 10px;
  background-color: #666666;
  border-radius: 5px;
  margin-left: -20px;
  margin-right: 10px;
}

.selected-div {
  display: flex;
}

.text_game {
  margin-left: 10px;
}

.title {
  margin-left: 20px;
}

.btn_logo:hover {
  background: #1d1d1d;
}

.btn_open_games {
  margin-left: 20px;
}

.btn_open_groups {
  margin-right: 20px;
}

.zone_post_and_team {
  margin-right: 12%;
}

.btn_small_devices {
  font-weight: bold;
  margin-right: 20px;
  display: none;
}

.btn_small_devices:hover {
  background: #ffd208;
  color: black;
  font-weight: bold;
}

.btn_post {
  font-weight: bold;
  margin-left: -30px;
  margin-right: 20px;
}

.btn_post:hover {
  background: #ffd208;
  color: black;
  font-weight: bold;
}

.btn_jointeam {
  font-weight: bold;
  margin-right: 20px;
}

.btn_jointeam:hover {
  background: #ffd208;
  color: black;
  font-weight: bold;
}

.ver_perfil_item {
  background: #1d1d1d;
  border-radius: 10px;
  color: white;
  width: 200px;
}

.ver_perfil_item:hover {
  transform: scale(1.05);
  font-weight: bold;
  background: #ffd208;
  color: black;
}

.log_out_item {
  background: red;
  color: white;
  border-radius: 10px;
  margin-top: 20px;
}

.log_out_item:hover {
  transform: scale(1.05);
  font-weight: bold;
}

.item_profile {
  text-align: center;
  background: #222222;
}

.item_section_profile {
  margin-left: 10%;
  margin-top: 5%;
  margin-bottom: 5%;
}

.profile {
  cursor: pointer;
}

.profile:hover {
  transform: scale(1.1);
}

.user_name {
  margin-top: 5%;
  margin-bottom: 5%;
  margin-right: 80%;
  font-weight: bold;
  font-size: 15px;
  color: rgb(255, 255, 255);
}

.imagem_avatar {
  width: 50px;
  height: 50px;
}

/*barra grupos e amigos*/

.box_amigos {
  height: 48%;
  margin-top: 20px;
}

.input_procurar {
  width: 90%;
  margin: -15px auto;
}

.users_in_group {
  background: #222222;
  padding-top: 5px;
  padding-bottom: 5px;
}

.user_in_group {
  cursor: pointer;
}

.user_in_group:hover {
  transform: scale(1.1);
}

.group_card {
  background: #000000;
  transition: transform 0.1s;
  width: 80%;
  margin: 10px auto;
  color: white;
  text-shadow: 1px 1px 6px black;
  font-weight: bold;
  border-radius: 10px;
}
.zona_cima_grupo {
  background-repeat: no-repeat;
  background-size: 290px;
  background-position: -50px;
}
.zona_cima_grupo:hover {
  filter: none;
}

.group_card:hover {
  transform: scale(1.05);
}

.friend_card {
  cursor: pointer;
  transition: transform 0.1s;
  width: 80%;
  margin: 10px auto;
}

.no-group {
  background: #000000;
  transition: transform 0.1s;
  color: #ffd208;
}

.friend_card:hover {
  transform: scale(1.05);
}

.group_image {
  width: 100%;
  height: 50px;
  background: #ffd208;
}

.divide_box {
  margin-top: 10%;
}

.amigos_text {
  margin-top: 10px;
}

.chat {
  z-index: 20;
  position: sticky;
  bottom: 0;
  transition: 0.5s ease;
}

.friend-modal {
  width: 50%;
}

.q-chip:hover {
  transform: scale(1.05);
  background: #ffd208;
  color: #000000;
}
.alert {
  padding: 20px;
  background-color: #f44336;
  color: white;
}

.closebtn {
  margin-left: 15px;
  color: white;
  font-weight: bold;
  float: right;
  font-size: 22px;
  line-height: 20px;
  cursor: pointer;
  transition: 0.3s;
}

.closebtn:hover {
  color: black;
}

.more {
  cursor: pointer;
}
.more:hover {
  transform: scale(1.05);
}

.add_friend_buttons:hover {
  transform: scale(1.05);
}

.unfollow_button:hover {
  transform: scale(1.05);
  font-weight: bold;
  text-decoration: underline;
}

.view-profile-text:hover {
  transform: scale(1.05);
  font-weight: bold;
  text-decoration: underline;
}

@media only screen and (max-width: 790px) {
  .btn_post {
    display: none;
  }
  .btn_jointeam {
    display: none;
  }

  .btn_small_devices {
    display: block;
  }
}

@media only screen and (max-height: 900px) {
  .box_amigos {
    height: 33%;
  }
}
</style>
