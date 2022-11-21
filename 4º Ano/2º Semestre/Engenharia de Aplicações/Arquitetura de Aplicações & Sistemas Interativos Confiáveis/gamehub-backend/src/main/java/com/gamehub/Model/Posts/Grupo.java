package com.gamehub.Model.Posts;


import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.gamehub.Model.Users.CaixaMensagens;
import com.gamehub.Model.Users.Gamer;

import javax.persistence.*;
import java.util.List;

@Entity
public class Grupo {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;

    @JsonIgnoreProperties({"estado", "amigos", "classificacao", "numero_classificacoes", "utilizador", "recompensas", "jogos", "caixasMensagens", "likedPosts", "dislikedPosts", "publicacoes_grupo", "publicacoes_media", "grupo"})
    @OneToMany(mappedBy = "grupo", fetch = FetchType.EAGER)
    private List<Gamer> gamers;

    @JsonIgnoreProperties(value = "grupo")
    @OneToOne(mappedBy = "grupo", cascade = CascadeType.ALL, fetch = FetchType.EAGER)
    private PostGrupo postGrupo;

    @JsonIgnore
    @OneToOne(cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    @JoinColumn(name = "caixamensagens_id")
    private CaixaMensagens caixaMensagens;

    @Transient
    private int id_caixa_mensagem;

    private String imageLink;

    public Grupo(int id, List<Gamer> gamers, PostGrupo postGrupo, String imageLink) {
        this.id = id;
        this.gamers = gamers;
        this.postGrupo = postGrupo;
        this.imageLink = imageLink;
    }

    public Grupo(List<Gamer> gamers, String imageLink) {
        this.gamers = gamers;
        this.caixaMensagens = new CaixaMensagens();
        this.imageLink = imageLink;
    }

    public Grupo() {

    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public List<Gamer> getGamers() {
        return gamers;
    }

    public void setGamers(List<Gamer> gamers) {
        this.gamers = gamers;
    }

    public PostGrupo getPostGrupo() {
        return postGrupo;
    }

    public void setPostGrupo(PostGrupo postGrupo) {
        this.postGrupo = postGrupo;
    }

    public CaixaMensagens getCaixaMensagens() {
        return caixaMensagens;
    }

    public void setCaixaMensagens(CaixaMensagens caixaMensagens) {
        this.caixaMensagens = caixaMensagens;
    }

    @Override
    public String toString() {
        return "Grupo{" +
                "id=" + id +
                ", gamers=" + gamers +
                ", postGrupo=" + postGrupo +
                '}';
    }

    /**
     * Método que verifica se um grupo já está completo
     * @return booleano que indica se o grupo já está cheio
     */
    public boolean is_full() {
        int num_max = this.postGrupo.getParticipantes();
        int atual = this.gamers.size();

        return atual >= num_max;
    }

    public int getId_caixa_mensagem() {
        return this.caixaMensagens.getId();
    }

    public void setId_caixa_mensagem(int id_caixa_mensagem) {

    }

    public String getImageLink() {
        return imageLink;
    }

    public void setImageLink(String imageLink) {
        this.imageLink = imageLink;
    }

    /**
     * Adiciona um novo participante a um grupo
     * @param gamer Gamer a adicionar ao grupo
     */
    public void add_participante(Gamer gamer) {
        this.gamers.add(gamer);
    }
}
