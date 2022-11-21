<template>
  <div class="chat">
    <div class="header_zone">
      <q-toolbar>
        <q-btn flat round dense class="q-mr-sm">
          <q-icon name="menu" color="white" />
        </q-btn>
        <q-toolbar-title v-if="members.postGrupo" class="text-white">{{
          members.postGrupo.nomeEquipa
        }}</q-toolbar-title>

        <q-btn
          flat
          round
          dense
          icon="close"
          color="white"
          class="q-mr-sm"
          @click="$emit('closeChat')"
        />
      </q-toolbar>
    </div>
    <q-scroll-area
      class="scroll-zone bg-dark"
      :thumb-style="thumbStyle"
      :bar-style="barStyle"
      ref="chatScroll"
    >
      <div class="q-pa-md q-px-lg column bg-dark" v-if="members.gamers">
        <q-chat-message
          class="cenas_do_chat text-white"
          v-for="(message, index) in messages"
          :key="index"
          :name="
            message.id_remetente == myId ? 'eu' : getName(message.id_remetente)
          "
          :avatar="getAvatar(message.id_remetente)"
          :text="[message.conteudo]"
          :text-color="message.id_remetente == myId ? 'white' : 'black'"
          :sent="message.id_remetente == myId ? true : false"
          :bg-color="message.id_remetente == myId ? 'accent' : 'secondary'"
        />
      </div>
    </q-scroll-area>
    <div class="bg-black" elevated>
      <q-toolbar>
        <q-form class="full-width" @submit="sendMessage">
          <q-input
            v-model="newMessage"
            bg-color="primary"
            label-color="white"
            input-style="color:white"
            outlined
            rounded
            label="Mensagem"
            dense
            autocomplete="off"
            ref="messageInput"
          >
            <q-btn round dense flat type="submit" color="white" icon="send" />
          </q-input>
        </q-form>
      </q-toolbar>
    </div>
  </div>
</template>

<script>
import { ref } from "@vue/reactivity";
import {
  onBeforeUnmount,
  onMounted,
  onUpdated,
  watch,
} from "@vue/runtime-core";
import { scroll } from "quasar";
const { setVerticalScrollPosition } = scroll;
import axios from "axios";
import URL from "../url.js";
export default {
  props: ["idGrupo"],
  setup(props) {
    const newMessage = ref("");
    const messages = ref([]);
    var interval = ref("");
    const members = ref([]);
    const messageInput = ref(null);

    const myId = ref("");
    const id_caixa = ref("");

    const sendMessage = async () => {
      if (newMessage.value != "") {
        messages.value.push({
          conteudo: newMessage.value,
          id_remetente: localStorage.id,
        });
        const dataMsg = newMessage.value;

        newMessage.value = "";

        await axios({
          method: "post",
          url: URL.URL + "/utilizador/addmensagemGrupo/" + id_caixa.value,
          params: {
            id_gamer: localStorage.id,
          },
          data: {
            conteudo: dataMsg,
          },
        });
      }
      messageInput.value.focus();
    };

    const chatScroll = ref(null);

    watch(
      () => [...messages.value],
      (val) => {
        if (Object.keys(val).length) {
          scrollToBottom();
        }
      }
    );

    const scrollToBottom = () => {
      const scrollArea = chatScroll.value;
      const scrollTarget = scrollArea.getScrollTarget();
      setTimeout(() => {
        setVerticalScrollPosition(
          scrollTarget,
          scrollTarget.scrollHeight + 200,
          0
        );
      }, 1);
    };

    onMounted(async () => {
      myId.value = localStorage.id;
      scrollToBottom();
      const result_members = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getGrupo/" + props.idGrupo,
      });
      const result_members_msgs = await result_members.data;
      members.value = result_members_msgs;
      id_caixa.value = result_members_msgs.id_caixa_mensagem;

      const result_msgs = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getmensagenscaixa/" + id_caixa.value,
      });
      const result_data_msgs = await result_msgs.data;
      messages.value = result_data_msgs;

      interval.value = setInterval(async () => {
        scrollToBottom();
        const result_msgs = await axios({
          method: "get",
          url: URL.URL + "/utilizador/getmensagenscaixa/" + id_caixa.value,
        });
        const result_data_msgs = await result_msgs.data;
        messages.value = result_data_msgs;
      }, 10000);
    });

    onUpdated(async () => {
      scrollToBottom();
      const result_msgs = await axios({
        method: "get",
        url: URL.URL + "/utilizador/getmensagenscaixa/" + id_caixa.value,
      });
      const result_data_msgs = await result_msgs.data;
      messages.value = result_data_msgs;
    });

    onBeforeUnmount(() => {
      clearInterval(interval.value);
    });

    const getName = (id) => {
      const result = members.value.gamers.filter((member) => member.id == id);
      return result[0].nome;
    };

    const getAvatar = (id) => {
      const result = members.value.gamers.filter((member) => member.id == id);
      return result[0].avatar.link;
    };

    return {
      myId,
      newMessage,
      messages,
      members,
      sendMessage,
      chatScroll,
      getName,
      getAvatar,
      messageInput,
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
    };
  },
  methods: {
    viewFriendProfile(id) {
      this.$emit("closeChat");
      this.$router.push("/friendProfile/" + id);
    },
  },
};
</script>

<style scoped>
.header_zone {
  background: black;
  height: 60px;
  padding-top: 5px;
}
.chat {
  width: 350px;
  left: 75%;
}

.scroll-zone {
  height: 400px;
}

.header_avatar {
  width: 50px;
  height: 50px;
}
</style>
